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

/-- External coordinates in a complete source box, retaining input/output order. -/
def boxExternal (D : LatticeData) (M : ℕ) :
    Internal D M ⊕ Internal D M → External D :=
  Sum.elim (fun i => (false, boxLabel D M i)) (fun i => (true, boxLabel D M i))

private theorem box_row (D : LatticeData) (M : ℕ) :
    originalRow D M (boxExternal D M) = correctedMatrix D (boxLabel D M) := by
  ext (i | (i | i)) (j | (j | j)) <;> rfl

private theorem box_mean (D : LatticeData) (a : Charge D) (M : ℕ) :
    originalMean D a M (boxExternal D M) = correctedMean D a (boxLabel D M) := by
  ext (i | (i | i)) <;> rfl

private theorem external_row_restrict {Y : Type*} [Fintype Y] [DecidableEq Y]
    (D : LatticeData) (M : ℕ) (e : Y → External D) (f : X ↪ Y) :
    let g := (Function.Embedding.refl (Internal D M)).sumMap f
    (fun i j => originalRow D M e (g i) (g j)) = originalRow D M (e ∘ f) ∧
    (fun i j => transportCovariance (sourceBlock (J := Y) (inverseSubstitution D M))
      (originalRow D M e) (g i) (g j)) =
      transportCovariance (sourceBlock (J := X) (inverseSubstitution D M))
        (originalRow D M (e ∘ f)) := by
  dsimp only
  constructor
  · ext (i | i) (j | j) <;> rfl
  · ext i j
    simp only [covariance_as_means]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp only [Function.Embedding.sumMap, Sum.map_inl,
          Function.Embedding.refl_apply, source_sum]
        apply Finset.sum_congr rfl
        intro c hc
        congr 1
      | inr j =>
        simp only [Function.Embedding.sumMap, Sum.map_inl, Sum.map_inr,
          Function.Embedding.refl_apply, source_sum]
        apply Finset.sum_congr rfl
        intro c hc
        congr 1
    | inr i =>
      cases j with
      | inl j =>
        simp only [Function.Embedding.sumMap, Sum.map_inl, Sum.map_inr,
          Function.Embedding.refl_apply, source_sum]
        apply Finset.sum_congr rfl
        intro c hc
        congr 1
      | inr j =>
        simp only [Function.Embedding.sumMap, Sum.map_inr, source_sum]
        rfl

private theorem external_mean_restrict {Y : Type*} [Fintype Y] [DecidableEq Y]
    (D : LatticeData) (a : Charge D) (M : ℕ) (e : Y → External D) (f : X ↪ Y) :
    let g := (Function.Embedding.refl (Internal D M)).sumMap f
    (fun i => originalMean D a M e (g i)) = originalMean D a M (e ∘ f) ∧
    (fun i => originalInverseMean D a M e (g i)) = originalInverseMean D a M (e ∘ f) := by
  dsimp only
  constructor
  · ext (i | i) <;> rfl
  · ext i
    unfold originalInverseMean
    cases i with
    | inl i =>
      simp only [Function.Embedding.sumMap, Sum.map_inl,
        Function.Embedding.refl_apply, source_sum]
      apply Finset.sum_congr rfl
      intro c hc
      congr 1
    | inr i =>
      simp only [Function.Embedding.sumMap, Sum.map_inr, source_sum]
      rfl

private theorem external_join {Y : Type*} [DecidableEq Y] (I : Type*) [DecidableEq I]
    (f : X ↪ Y) (d : I →₀ ℕ) (h : X →₀ ℕ) :
    (d.sumElim h).embDomain ((Function.Embedding.refl I).sumMap f) =
      d.sumElim (h.embDomain f) := by
  ext i
  cases i with
  | inl i =>
    simpa using Finsupp.embDomain_apply_self
      ((Function.Embedding.refl I).sumMap f) (d.sumElim h) (.inl i)
  | inr i =>
    by_cases hi : i ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hi
      simpa using Finsupp.embDomain_apply_self
        ((Function.Embedding.refl I).sumMap f) (d.sumElim h) (.inr j)
    · rw [Finsupp.embDomain_of_notMem_range, Finsupp.sumElim_inr,
        Finsupp.embDomain_of_notMem_range _ _ _ hi]
      rintro ⟨j | j, hj⟩
      · cases hj
      · exact hi ⟨j, Sum.inr.inj hj⟩

/-- Restrict external coordinates only after complete inverse-colour transport.
The common source box and both full row occupations are unchanged. -/
theorem original_external_box_coefficients (D : LatticeData) (a : Charge D) (M : ℕ)
    (f : X ↪ Internal D M ⊕ Internal D M) (d : Internal D M →₀ ℕ) (h : X →₀ ℕ) :
    let A := correctedMatrix D (boxLabel D M)
    let U := sourceBlock (J := Internal D M ⊕ Internal D M) (inverseSubstitution D M)
    OriginalChargedRowSource.affineCoefficient A (correctedMean D a (boxLabel D M))
        (d.sumElim (h.embDomain f)) =
      OriginalChargedRowSource.affineCoefficient (originalRow D M (boxExternal D M ∘ f))
        (originalMean D a M (boxExternal D M ∘ f)) (d.sumElim h) ∧
    OriginalChargedRowSource.affineCoefficient (transportCovariance U A)
        (transportMean U (correctedMean D (-a) (boxLabel D M)))
        (d.sumElim (h.embDomain f)) =
      OriginalChargedRowSource.affineCoefficient
        (transportCovariance (sourceBlock (J := X) (inverseSubstitution D M))
          (originalRow D M (boxExternal D M ∘ f)))
        (originalInverseMean D a M (boxExternal D M ∘ f)) (d.sumElim h) := by
  dsimp only
  rw [← box_row, ← box_mean D a, ← box_mean D (-a)]
  let g := (Function.Embedding.refl (Internal D M)).sumMap f
  have hc := external_row_restrict D M (boxExternal D M) f
  have hm := external_mean_restrict D a M (boxExternal D M) f
  have ht := affine_enlarge (originalRow D M (boxExternal D M))
    (originalMean D a M (boxExternal D M)) g (d.sumElim h)
  have hu := affine_enlarge
    (transportCovariance (sourceBlock (J := Internal D M ⊕ Internal D M)
      (inverseSubstitution D M)) (originalRow D M (boxExternal D M)))
    (originalInverseMean D a M (boxExternal D M)) g (d.sumElim h)
  simp only [g, external_join] at ht hu
  rw [hc.1, hm.1] at ht
  rw [hc.2, hm.2] at hu
  exact ⟨ht, hu⟩

/-- The four fixed external supports share a single finite label type. -/
def fourSupport (D : LatticeData) (betaL gammaL betaR gammaR : Exponent D) : Finset (Index D) :=
  betaL.support ∪ gammaL.support ∪ betaR.support ∪ gammaR.support

/-- Input and output coordinates of one compact external row. -/
abbrev CompactExternal (D : LatticeData) (F : Finset (Index D)) :=
  {b // b ∈ F} ⊕ {b // b ∈ F}

/-- Literal compact input/output labels, without duplicating source coordinates. -/
def compactExternal (D : LatticeData) (F : Finset (Index D)) : CompactExternal D F → External D :=
  Sum.elim (fun b => (false, b.val)) (fun b => (true, b.val))

/-- Ordinary occupations in left-input/left-output/right-input/right-output order. -/
def externalOccupation (D : LatticeData) (F : Finset (Index D))
    (betaL gammaL betaR gammaR : Exponent D) :
    (CompactExternal D F ⊕ CompactExternal D F) →₀ ℕ :=
  ((restricted D F betaL).sumElim (restricted D F gammaL)).sumElim
    ((restricted D F betaR).sumElim (restricted D F gammaR))

private def supportToBox (D : LatticeData) (F : Finset (Index D)) (M : ℕ)
    (hF : ∀ b ∈ F, b.2 < M) : {b // b ∈ F} ↪ Internal D M where
  toFun b := (b.val.1, ⟨b.val.2, hF b.val b.property⟩)
  inj' := by
    intro b c he
    apply Subtype.ext
    exact Prod.ext (congrArg (fun i : Internal D M => i.1) he)
      (congrArg (fun i : Internal D M => i.2.val) he)

private theorem restricted_box (D : LatticeData) (F : Finset (Index D)) (M : ℕ)
    (hF : ∀ b ∈ F, b.2 < M) (p : Exponent D) (hp : p.support ⊆ F) :
    (restricted D F p).embDomain (supportToBox D F M hF) = boxOccupation D M p := by
  apply Finsupp.embDomain_injective (boxLabel D M)
  rw [← Finsupp.embDomain_trans_apply]
  have he : (supportToBox D F M hF).trans (boxLabel D M) = supportLabel D F := rfl
  rw [he, restricted_reconstruct D F p hp,
    box_reconstruct D M p (fun b hb => hF b (hp hb))]

private theorem sum_embDomain {I J K L : Type*} [DecidableEq I] [DecidableEq J]
    [DecidableEq K] [DecidableEq L] (f : I ↪ K) (g : J ↪ L) (d : I →₀ ℕ) (h : J →₀ ℕ) :
    (d.sumElim h).embDomain (f.sumMap g) = (d.embDomain f).sumElim (h.embDomain g) := by
  ext i
  cases i with
  | inl i =>
    by_cases hi : i ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hi
      simpa using Finsupp.embDomain_apply_self (f.sumMap g) (d.sumElim h) (.inl j)
    · rw [Finsupp.embDomain_of_notMem_range, Finsupp.sumElim_inl,
        Finsupp.embDomain_of_notMem_range _ _ _ hi]
      rintro ⟨j | j, hj⟩
      · exact hi ⟨j, Sum.inl.inj hj⟩
      · cases hj
  | inr i =>
    by_cases hi : i ∈ Set.range g
    · obtain ⟨j, rfl⟩ := hi
      simpa using Finsupp.embDomain_apply_self (f.sumMap g) (d.sumElim h) (.inr j)
    · rw [Finsupp.embDomain_of_notMem_range, Finsupp.sumElim_inr,
        Finsupp.embDomain_of_notMem_range _ _ _ hi]
      rintro ⟨j | j, hj⟩
      · cases hj
      · exact hi ⟨j, Sum.inr.inj hj⟩

/-- The compact occupations give precisely both literal common-box rows.
Every colour is summed before restricting the right covariance or mean. -/
theorem original_compact_box_coefficients (D : LatticeData) (a : Charge D)
    (F : Finset (Index D)) (M : ℕ) (hF : ∀ b ∈ F, b.2 < M)
    (beta gamma : Exponent D) (hb : beta.support ⊆ F) (hg : gamma.support ⊆ F)
    (d : Internal D M →₀ ℕ) :
    let h := (restricted D F beta).sumElim (restricted D F gamma)
    let A := correctedMatrix D (boxLabel D M)
    let U := sourceBlock (J := Internal D M ⊕ Internal D M) (inverseSubstitution D M)
    OriginalChargedRowSource.affineCoefficient A (correctedMean D a (boxLabel D M))
        (threeOccupation d (boxOccupation D M beta) (boxOccupation D M gamma)) =
      OriginalChargedRowSource.affineCoefficient (originalRow D M (compactExternal D F))
        (originalMean D a M (compactExternal D F)) (d.sumElim h) ∧
    OriginalChargedRowSource.affineCoefficient (transportCovariance U A)
        (transportMean U (correctedMean D (-a) (boxLabel D M)))
        (threeOccupation d (boxOccupation D M beta) (boxOccupation D M gamma)) =
      OriginalChargedRowSource.affineCoefficient
        (transportCovariance (sourceBlock (J := CompactExternal D F) (inverseSubstitution D M))
          (originalRow D M (compactExternal D F)))
        (originalInverseMean D a M (compactExternal D F)) (d.sumElim h) := by
  let f := (supportToBox D F M hF).sumMap (supportToBox D F M hF)
  have he : boxExternal D M ∘ f = compactExternal D F := by
    ext (i | i) <;> rfl
  have hh := original_external_box_coefficients D a M f d
    ((restricted D F beta).sumElim (restricted D F gamma))
  rw [he, sum_embDomain, restricted_box D F M hF beta hb,
    restricted_box D F M hF gamma hg] at hh
  exact hh

/-- The original Wick energy contraction in the actual compact external family.
The common box is arbitrary above the energy and all four supports. -/
theorem original_fixed_energy_compact (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (betaL gammaL betaR gammaR : Exponent D) (eL eR : ℤ)
    (n M : ℕ) (hn : n < M)
    (hF : ∀ b ∈ fourSupport D betaL gammaL betaR gammaR, b.2 < M) :
    (∑ᶠ alpha : Exponent D, if oscillatorEnergy alpha = n then
      chargeScalar D a * chargeScalar D (-a) *
        wick D (monomial gammaL 1) (oscillatorCorrected D hu a eL
          (monomial alpha 1) (monomial betaL 1)) *
        wick D (monomial gammaR 1) (oscillatorCorrected D hu (-a) eR
          (dualOscillatorMonomial D alpha) (monomial betaR 1)) else 0) =
    let F := fourSupport D betaL gammaL betaR gammaR
    let e := compactExternal D F
    let h := (restricted D F betaL).sumElim (restricted D F gammaL)
    let k := (restricted D F betaR).sumElim (restricted D F gammaR)
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
          OriginalChargedRowSource.affineCoefficient (originalRow D M e)
            (originalMean D a M e) (d.val.sumElim h) *
          OriginalChargedRowSource.affineCoefficient
            (transportCovariance (sourceBlock (J := CompactExternal D F) (inverseSubstitution D M))
              (originalRow D M e))
            (originalInverseMean D a M e) (d.val.sumElim k) := by
  classical
  let F := fourSupport D betaL gammaL betaR gammaR
  have hbL : betaL.support ⊆ F := by intro b hb; simp [F, fourSupport, hb]
  have hgL : gammaL.support ⊆ F := by intro b hb; simp [F, fourSupport, hb]
  have hbR : betaR.support ⊆ F := by intro b hb; simp [F, fourSupport, hb]
  have hgR : gammaR.support ⊆ F := by intro b hb; simp [F, fourSupport, hb]
  rw [original_fixed_energy_common_box D hu a betaL gammaL betaR gammaR eL eR n M hn
    (fun b hb => hF b (hbL hb)) (fun b hb => hF b (hgL hb))
    (fun b hb => hF b (hbR hb)) (fun b hb => hF b (hgR hb))]
  dsimp only
  congr 1
  apply finsum_congr
  intro d
  rw [(original_compact_box_coefficients D a F M hF betaL gammaL hbL hgL d.val).1,
    (original_compact_box_coefficients D a F M hF betaR gammaR hbR hgR d.val).2]

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction
