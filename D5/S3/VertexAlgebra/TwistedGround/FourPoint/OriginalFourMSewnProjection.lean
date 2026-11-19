/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSewnProjection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSewnProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four original occupation sums from one native sewn Gaussian polynomial readout. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMProjectionModes

/-! The readout of the joined oscillator polynomials in the native order
expands into the original four rectangular occupation sums. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSewnProjection

open MvPolynomial LatticeGeneratingFieldLocality
open OriginalFourMJointWick (BoundedExternal)
open OriginalFourMProjectionModes (bounded_external_sewn_charge)
open OriginalGaussianSourceRestriction (CompactExternal externalOccupation fourSupport)
open OriginalGaussianSewnAnalytic (sewn)
open OriginalFourMChargeNormal (sewnChargeTerm)
open OriginalNormalRowSource (restricted restricted_reconstruct supportLabel)
open LatticePositiveEnergy (chargeEnergy)
open LatticeHalfFockChargedTensorCoefficients (chargeScalar)
open FactorialFockMetric (weight)
open private externalLabel from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMJointWick
open private compactEmbedding from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMProjectionModes

open OriginalFourMSignedOverlap (taggedMode)
open private boundedWord nativeLabel from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMJointWick

private abbrev NativeModes (D : LatticeData) (N : ℕ) :=
  BoundedExternal D N ⊕ BoundedExternal D N

private def boxedOscillator (D : LatticeData) (N : ℕ) (leg out : Bool) :
    Oscillator D →ₐ[ℂ] MvPolynomial (NativeModes D N) ℂ :=
  aeval fun i : Index D => if h : i.2 < N + 1 then
    X (taggedMode leg (out, i.1, ⟨i.2, h⟩)) else 0

private def compactTag (D : LatticeData) (F : Finset (Index D)) (leg out : Bool)
    (i : {j // j ∈ F}) : CompactExternal D F ⊕ CompactExternal D F :=
  taggedMode leg (taggedMode out i)

private theorem boxed_monomial (D : LatticeData) (N : ℕ) (F : Finset (Index D))
    (hF : ∀ i ∈ F, i.2 ≤ N) (leg out : Bool)
    (d : Index D →₀ ℕ) (hd : d.support ⊆ F) (c : ℂ) :
    boxedOscillator D N leg out (monomial d c) =
      monomial ((restricted D F d).mapDomain
        (fun i => ((compactEmbedding D N F hF).sumMap (compactEmbedding D N F hF))
          (compactTag D F leg out i))) c := by
  classical
  let f := compactEmbedding D N F hF
  let tag := fun i => (f.sumMap f) (compactTag D F leg out i)
  have hs : rename (supportLabel D F) (monomial (restricted D F d) c) = monomial d c := by
    rw [rename_monomial, ← Finsupp.embDomain_eq_mapDomain, restricted_reconstruct D F d hd]
  have hf : (boxedOscillator D N leg out).comp (rename (supportLabel D F)) = rename tag := by
    apply MvPolynomial.algHom_ext
    intro i
    have hi : i.val.2 < N + 1 := Nat.lt_succ_of_le (hF i.val i.property)
    simp only [AlgHom.comp_apply, rename_X, boxedOscillator, aeval_X]
    change (if h : i.val.2 < N + 1 then
      X (taggedMode leg (out, i.val.1, ⟨i.val.2, h⟩)) else 0) = X (tag i)
    rw [dite_eq_left hi]
    cases leg <;> cases out <;> rfl
  rw [← hs, ← AlgHom.comp_apply, hf, rename_monomial]

private theorem boxed_monomials_product (D : LatticeData) (N : ℕ)
    (d g r s : Index D →₀ ℕ) (a b c e : ℂ)
    (hF : ∀ i ∈ fourSupport D d g r s, i.2 ≤ N) :
    let F := fourSupport D d g r s
    let f := compactEmbedding D N F hF
    boxedOscillator D N false false (monomial d a) *
      boxedOscillator D N false true (monomial g b) *
      boxedOscillator D N true false (monomial r c) *
      boxedOscillator D N true true (monomial s e) =
      monomial ((externalOccupation D F d g r s).embDomain (f.sumMap f)) (a * b * c * e) := by
  classical
  dsimp only
  let F := fourSupport D d g r s
  rw [boxed_monomial D N F hF false false d (by intro i hi; simp [F, fourSupport, hi]),
    boxed_monomial D N F hF false true g (by intro i hi; simp [F, fourSupport, hi]),
    boxed_monomial D N F hF true false r (by intro i hi; simp [F, fourSupport, hi]),
    boxed_monomial D N F hF true true s (by intro i hi; simp [F, fourSupport, hi])]
  simp only [monomial_mul_monomial]
  congr 1
  simp only [externalOccupation, Finsupp.embDomain_eq_mapDomain, Finsupp.sumElim_eq_add,
    Finsupp.mapDomain_add, ← Finsupp.mapDomain_fun_comp, Function.comp_def, add_assoc]
  rfl

private def sewnReadout (D : LatticeData) (q : Charge D) (N : ℕ) (w : ℂ) :
    MvPolynomial (NativeModes D N) ℂ →ₗ[ℂ] ℂ :=
  (basisMonomials (NativeModes D N) ℂ).constr ℂ fun e =>
    (weight e : ℂ) * ((chargeScalar D q * chargeScalar D (-q)) *
      w ^ (2 * (chargeEnergy D q).toNat) * sewn D q (externalLabel D N) e w)

private theorem sewnReadout_monomial (D : LatticeData) (q : Charge D) (N : ℕ) (w : ℂ)
    (d : NativeModes D N →₀ ℕ) (a : ℂ) :
    sewnReadout D q N w (monomial d a) =
      a * ((weight d : ℂ) * ((chargeScalar D q * chargeScalar D (-q)) *
        w ^ (2 * (chargeEnergy D q).toNat) * sewn D q (externalLabel D N) d w)) := by
  rw [show (monomial d a : MvPolynomial (NativeModes D N) ℂ) = a • monomial d 1 by
    simp [smul_monomial, smul_eq_mul], map_smul]
  change a • (basisMonomials (NativeModes D N) ℂ).constr ℂ _
    ((basisMonomials (NativeModes D N) ℂ) d) = _
  rw [Module.Basis.constr_basis, smul_eq_mul]

private theorem sum_reverse_four {ι κ ν τ : Type*} (I : Finset ι) (J : Finset κ)
    (K : Finset ν) (T : Finset τ) (f : ι → κ → ν → τ → ℂ) :
    (∑ t ∈ T, ∑ k ∈ K, ∑ j ∈ J, ∑ i ∈ I, f i j k t) =
      ∑ i ∈ I, ∑ j ∈ J, ∑ k ∈ K, ∑ t ∈ T, f i j k t := by
  calc
    _ = ∑ t ∈ T, ∑ k ∈ K, ∑ i ∈ I, ∑ j ∈ J, f i j k t := by
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ t ∈ T, ∑ i ∈ I, ∑ k ∈ K, ∑ j ∈ J, f i j k t := by
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i ∈ I, ∑ t ∈ T, ∑ k ∈ K, ∑ j ∈ J, f i j k t := Finset.sum_comm
    _ = ∑ i ∈ I, ∑ t ∈ T, ∑ j ∈ J, ∑ k ∈ K, f i j k t := by
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i ∈ I, ∑ j ∈ J, ∑ t ∈ T, ∑ k ∈ K, f i j k t := by
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- The single native Gaussian readout of the joined four oscillator
polynomials expands into the literal four original occupation sums in
native left-input, left-output, right-input, right-output order. -/
theorem boxed_four_sewn_projection (D : LatticeData) (q : Charge D) (N : ℕ) (w : ℂ)
    (P Q R S : Oscillator D)
    (hP : ∀ d ∈ P.support, ∀ i ∈ d.support, i.2 ≤ N)
    (hQ : ∀ d ∈ Q.support, ∀ i ∈ d.support, i.2 ≤ N)
    (hR : ∀ d ∈ R.support, ∀ i ∈ d.support, i.2 ≤ N)
    (hS : ∀ d ∈ S.support, ∀ i ∈ d.support, i.2 ≤ N) :
    let F := boxedOscillator D N false false P * boxedOscillator D N false true Q *
      boxedOscillator D N true false R * boxedOscillator D N true true S
    (∑ d ∈ F.support, F.coeff d * ((weight d : ℂ) *
      ((chargeScalar D q * chargeScalar D (-q)) * w ^ (2 * (chargeEnergy D q).toNat) *
        sewn D q (externalLabel D N) d w))) =
      ∑ d ∈ P.support, ∑ g ∈ Q.support, ∑ r ∈ R.support, ∑ s ∈ S.support,
        (P.coeff d * Q.coeff g * R.coeff r * S.coeff s) *
          ((weight d : ℂ) * (weight g : ℂ) * (weight r : ℂ) * (weight s : ℂ)) *
          sewnChargeTerm D d g r s q w := by
  classical
  dsimp only
  let F := boxedOscillator D N false false P * boxedOscillator D N false true Q *
    boxedOscillator D N true false R * boxedOscillator D N true true S
  have hRead : sewnReadout D q N w F = ∑ d ∈ F.support, F.coeff d * ((weight d : ℂ) *
      ((chargeScalar D q * chargeScalar D (-q)) * w ^ (2 * (chargeEnergy D q).toNat) *
        sewn D q (externalLabel D N) d w)) := by
    conv_lhs => rw [F.as_sum]
    simp only [map_sum, sewnReadout_monomial]
  rw [← hRead]
  dsimp only [F]
  conv_lhs => rw [P.as_sum, Q.as_sum, R.as_sum, S.as_sum]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [sum_reverse_four]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  have hF : ∀ i ∈ fourSupport D d g r s, i.2 ≤ N := by
    intro i hi
    simp only [fourSupport, Finset.mem_union] at hi
    rcases hi with ((hi | hi) | hi) | hi
    · exact hP d hd i hi
    · exact hQ g hg i hi
    · exact hR r hr i hi
    · exact hS s hs i hi
  rw [boxed_monomials_product D N d g r s _ _ _ _ hF, sewnReadout_monomial,
    bounded_external_sewn_charge D q N d g r s w hF]
  ring

open OriginalFourMActualChart (Chart Puncture parameter)
open OriginalFourMOccupationTransport (flags)
open OriginalFourMCauchyTaylor (inverseLoweredWord)
open OriginalFourMSpatialWick (radial_spatial_sewn_charge spatialCoefficient)
open NativeAffineExternalCoefficient (coordinateJet)
open D5.S3.Analytic.OriginalHalfBinomialNome (Q0)
open private physicalEntry physicalMean from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWick
open private chartPeriod chartTau from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct
open private relative from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance

private def firstLeft : Chart → Puncture
  | .A | .D => .P
  | .B => .Q

private def secondLeft : Chart → Puncture
  | .A => .Q
  | .B | .D => .R

private def firstRight : Chart → Puncture
  | .A => .R
  | .B => .P
  | .D => .Q

private def punctureWords {X : Type*} (words : Puncture → List X) :
    List (Puncture × List X) :=
  [(.P, words .P), (.Q, words .Q), (.R, words .R), (.S, words .S)]

/-- The simultaneous Taylor coefficient of a charge summand equals the
literal four-occupation charge projection after all four inverse transforms.
The same order of physical marks is used in both radial charts. The common
mode box contains every supported mode in the four inverse-lowered words. -/
theorem radial_spatial_four_occupation (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (q : Charge D) (N : ℕ) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (upperA : Bool)
    (c : Chart) (hc : c = .A ∨ c = .B) {w : ℂ} (hw : ‖w‖ < 1)
    (hwc : w ^ 2 = parameter c x)
    (hNome : Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x) = Q0 (w ^ 2))
    {X : Type*} [Fintype X] [DecidableEq X]
    (slot : X → Puncture) (mode : X → Index D) (bound : ∀ i, (mode i).2 ≤ N)
    (words : Puncture → List X) (hslot : ∀ s j, j ∈ words s → slot j = s)
    (hl : ((punctureWords words).flatMap Prod.snd).Nodup)
    (hbox : ∀ s d, d ∈ (inverseLoweredWord D c x s ((words s).map mode)).support →
      ∀ i ∈ d.support, i.2 ≤ N) :
    let l := (punctureWords words).flatMap Prod.snd
    let colour := fun i => (mode i).1
    let sign := fun i => relative c (slot i)
    let K := physicalEntry D upperA c x slot colour
    let m := physicalMean D q upperA c x slot colour
    let W := fun s => inverseLoweredWord D c x s ((words s).map mode)
    let P := W (firstLeft c)
    let Q := W (secondLeft c)
    let R := W (firstRight c)
    let S := W .S
    spatialCoefficient (fun i => (mode i).2) l (fun u =>
      (chartPeriod upperA c x ^ (12 : ℕ))⁻¹ *
      Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x * (bilinear D q q : ℂ) / 2) *
      coordinateJet l (fun v => Complex.exp (
        (1 / 2 : ℂ) * (∑ i, ∑ j, K i j (u i) (u j) * (sign i * v i) * (sign j * v j)) +
          ∑ i, m i (u i) * (sign i * v i))) 0) 0 =
      (l.map sign).prod * (1 - w ^ 2) ^ (3 : ℕ) *
        ∑ d ∈ P.support, ∑ g ∈ Q.support, ∑ r ∈ R.support, ∑ s ∈ S.support,
          (P.coeff d * Q.coeff g * R.coeff r * S.coeff s) *
            ((weight d : ℂ) * (weight g : ℂ) * (weight r : ℂ) * (weight s : ℂ)) *
            sewnChargeTerm D d g r s q w := by
  classical
  dsimp only
  have hslots : ((punctureWords words).map Prod.fst).Nodup := by
    simp [punctureWords]
  have hv : ∀ entry ∈ punctureWords words, ∀ j ∈ entry.2, slot j = entry.1 := by
    intro entry he
    simp only [punctureWords, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> exact hslot _
  let W := fun s => inverseLoweredWord D c x s ((words s).map mode)
  let F := boxedOscillator D N false false (W (firstLeft c)) *
    boxedOscillator D N false true (W (secondLeft c)) *
    boxedOscillator D N true false (W (firstRight c)) *
    boxedOscillator D N true true (W .S)
  have hF : ((punctureWords words).map
      (fun entry => boundedWord D N c x entry.1 (entry.2.map mode))).prod = F := by
    cases c <;>
      simp only [punctureWords, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one, F, W, firstLeft, secondLeft, firstRight, boundedWord, boxedOscillator,
        nativeLabel, flags] <;> ac_rfl
  have h := radial_spatial_sewn_charge D hu hD h24 q N hx hx₁ upperA c hc hw hwc hNome
    slot mode bound (punctureWords words) hslots hv hl
  dsimp only at h
  rw [h, hF]
  congr 1
  exact boxed_four_sewn_projection D q N w (W (firstLeft c)) (W (secondLeft c))
    (W (firstRight c)) (W .S) (hbox _) (hbox _) (hbox _) (hbox _)

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSewnProjection
