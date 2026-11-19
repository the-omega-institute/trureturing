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

open Filter
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge reduceCharge)
open OriginalFourMPhysicalProduct (physicalProduct)
open OriginalFourMSpatialWick (physical_chart_jet_hasSum)
open NativeAffineExternalCoefficient (coordinateJet_const_mul)
open private chart_charge_data physicalChargeSummand markedQuadratic split_spatial
  mark_coefficient_eq_jet spatialCoefficient_const_mul from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWick

/-- The Taylor jet of the actual radial sector is the convergent sum over
its original charge fibre of the literal four-occupation projections. -/
theorem radial_sector_four_occupation (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (a : ModTwoCharge D) (N : ℕ) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (upperA : Bool)
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
    let W := fun s => inverseLoweredWord D c x s ((words s).map mode)
    let P := W (firstLeft c)
    let Q := W (secondLeft c)
    let R := W (firstRight c)
    let S := W .S
    HasSum (fun q : {q : Charge D // reduceCharge D q = a} =>
      (l.map sign).prod * (1 - w ^ 2) ^ (3 : ℕ) *
        ∑ d ∈ P.support, ∑ g ∈ Q.support, ∑ r ∈ R.support, ∑ s ∈ S.support,
          (P.coeff d * Q.coeff g * R.coeff r * S.coeff s) *
            ((weight d : ℂ) * (weight g : ℂ) * (weight r : ℂ) * (weight s : ℂ)) *
            sewnChargeTerm D d g r s q.val w)
      (spatialCoefficient (Sum.elim (fun i => (mode i).2) (fun _ => 1))
        (l.map Sum.inr ++ l.map Sum.inl) (fun z =>
          physicalProduct D hu slot colour upperA x c a (z ∘ Sum.inl) (z ∘ Sum.inr)) 0) := by
  classical
  dsimp only
  let l := (punctureWords words).flatMap Prod.snd
  let colour := fun i => (mode i).1
  have hp := chart_charge_data upperA c hx hx₁
  have hs := physical_chart_jet_hasSum D hu hD slot colour upperA c hx hx₁ hp.1 hp.2 a
    (Sum.elim (fun i => (mode i).2) (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl)
  refine hs.congr_fun ?_
  intro q
  have h := radial_spatial_four_occupation D hu hD h24 q.val N hx hx₁ upperA c hc hw hwc hNome
    slot mode bound words hslot hl hbox
  dsimp only at h
  rw [← h, split_spatial]
  rw [← congrFun (spatialCoefficient_const_mul _ _ _ _) 0]
  apply congrArg (fun f => spatialCoefficient (fun i => (mode i).2) l f 0)
  funext u
  rw [mark_coefficient_eq_jet l hl _ 0 (fun _ _ => rfl)]
  simp only [physicalChargeSummand, markedQuadratic, Sum.elim_inl, Sum.elim_inr,
    coordinateJet_const_mul, colour, mul_assoc]
  rfl

open LatticeDiscriminantTheta (gramReal)
open OriginalFourMChargeCoset (fourierSign quadraticSign)
open OriginalFourMProjectionModes (physical_chart_coefficient_overlap_normalized)

private def radialOccupationSection (D : LatticeData) {X : Type*} (slot : X → Puncture)
    (mode : X → Index D) (words : Puncture → List X) (c : Chart) (x : ℝ) (w : ℂ)
    (a : ModTwoCharge D) : ℂ :=
  let l := (punctureWords words).flatMap Prod.snd
  let W := fun s => inverseLoweredWord D c x s ((words s).map mode)
  let P := W (firstLeft c)
  let Q := W (secondLeft c)
  let R := W (firstRight c)
  let S := W .S
  ∑' q : {q : Charge D // reduceCharge D q = a},
    (l.map fun i => relative c (slot i)).prod * (1 - w ^ 2) ^ (3 : ℕ) *
      ∑ d ∈ P.support, ∑ g ∈ Q.support, ∑ r ∈ R.support, ∑ s ∈ S.support,
        (P.coeff d * Q.coeff g * R.coeff r * S.coeff s) *
          ((weight d : ℂ) * (weight g : ℂ) * (weight r : ℂ) * (weight s : ℂ)) *
          sewnChargeTerm D d g r s q.val w

/-- The rank-24 Fourier overlap on the actual A and B radial occupation
sums and the actual D chart jet, with the B normalization `x⁻⁶`.
Each radial nome equation refers to the original scalar nome. -/
theorem radial_occupation_section_overlap (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (h24 : D.rank = 24)
    (a : ModTwoCharge D) (N : ℕ) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (upperA : Bool)
    {wA wB : ℂ} (hwA : ‖wA‖ < 1) (hwB : ‖wB‖ < 1)
    (hsA : wA ^ 2 = parameter .A x) (hsB : wB ^ 2 = parameter .B x)
    (hNomeA : Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA .A x) = Q0 (wA ^ 2))
    (hNomeB : Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA .B x) = Q0 (wB ^ 2))
    {X : Type*} [Fintype X] [DecidableEq X]
    (slot : X → Puncture) (mode : X → Index D) (bound : ∀ i, (mode i).2 ≤ N)
    (words : Puncture → List X) (hslot : ∀ s j, j ∈ words s → slot j = s)
    (hl : ((punctureWords words).flatMap Prod.snd).Nodup)
    (hbox : ∀ c s d, d ∈ (inverseLoweredWord D c x s ((words s).map mode)).support →
      ∀ i ∈ d.support, i.2 ≤ N) :
    let A := radialOccupationSection D slot mode words .A x wA
    let B := radialOccupationSection D slot mode words .B x wB
    let l := (punctureWords words).flatMap Prod.snd
    let d := spatialCoefficient (Sum.elim (fun i => (mode i).2) (fun _ => 1))
      (l.map Sum.inr ++ l.map Sum.inl) (fun z =>
        physicalProduct D hu slot (fun i => (mode i).1) upperA x .D a
          (z ∘ Sum.inl) (z ∘ Sum.inr)) 0
    (2 : ℂ) ^ (12 : ℕ) * d = ∑ b, fourierSign D a b * A b ∧
    (2 : ℂ) ^ (12 : ℕ) * ((x : ℂ) ^ (6 : ℕ))⁻¹ * B a =
      ∑ b, fourierSign D a b * quadraticSign D b * A b := by
  dsimp only
  let l := (punctureWords words).flatMap Prod.snd
  let n : X ⊕ X → ℕ := Sum.elim (fun i => (mode i).2) (fun _ => 1)
  let k := l.map Sum.inr ++ l.map Sum.inl
  let J := fun c b =>
    spatialCoefficient n k (fun z =>
      physicalProduct D hu slot (fun i => (mode i).1) upperA x c b (z ∘ Sum.inl) (z ∘ Sum.inr)) 0
  have hA (b : ModTwoCharge D) : radialOccupationSection D slot mode words .A x wA b = J .A b :=
    (radial_sector_four_occupation D hu hD h24 b N hx hx₁ upperA .A (Or.inl rfl)
      hwA hsA hNomeA slot mode bound words hslot hl (hbox .A)).tsum_eq
  have hB : radialOccupationSection D slot mode words .B x wB a = J .B a :=
    (radial_sector_four_occupation D hu hD h24 a N hx hx₁ upperA .B (Or.inr rfl)
      hwB hsB hNomeB slot mode bound words hslot hl (hbox .B)).tsum_eq
  simp only [hA, hB]
  exact physical_chart_coefficient_overlap_normalized D hu hD h24
    slot (fun i => (mode i).1) upperA hx hx₁ hsA hwA n k a

open LatticeHalfFockChargedCoefficients (omega)
open OriginalFourMChargeCoset (oscillatorLower)
open OriginalFourMProjectionModes (project_occupations_on_signed_diagonal)
open private projectOccupations from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeNormal

private def modesBounded (D : LatticeData) (N : ℕ) (P : Oscillator D) : Prop :=
  ∀ d ∈ P.support, ∀ i ∈ d.support, i.2 ≤ N

private theorem sewnReadout_four (D : LatticeData) (q : Charge D) (N : ℕ) (w : ℂ)
    (P Q R S : Oscillator D) (hP : modesBounded D N P) (hQ : modesBounded D N Q)
    (hR : modesBounded D N R) (hS : modesBounded D N S) :
    sewnReadout D q N w (boxedOscillator D N false false P * boxedOscillator D N false true Q *
      boxedOscillator D N true false R * boxedOscillator D N true true S) =
      ∑ d ∈ P.support, ∑ g ∈ Q.support, ∑ r ∈ R.support, ∑ s ∈ S.support,
        (P.coeff d * Q.coeff g * R.coeff r * S.coeff s) *
          ((weight d : ℂ) * (weight g : ℂ) * (weight r : ℂ) * (weight s : ℂ)) *
          sewnChargeTerm D d g r s q w := by
  classical
  let F := boxedOscillator D N false false P * boxedOscillator D N false true Q *
    boxedOscillator D N true false R * boxedOscillator D N true true S
  change sewnReadout D q N w F = _
  calc
    _ = ∑ d ∈ F.support, F.coeff d * ((weight d : ℂ) *
        ((chargeScalar D q * chargeScalar D (-q)) * w ^ (2 * (chargeEnergy D q).toNat) *
          sewn D q (externalLabel D N) d w)) := by
      conv_lhs => rw [F.as_sum]
      simp only [map_sum, sewnReadout_monomial]
    _ = _ := boxed_four_sewn_projection D q N w P Q R S hP hQ hR hS

private def loweringSum (D : LatticeData) (K : ℕ) (P : Oscillator D) : Oscillator D :=
  ∑ j ∈ Finset.range K,
    ((-1 : ℂ) ^ j / (j.factorial : ℂ)) • (oscillatorLower D ^ j) P

/-- The original signed-diagonal projection of a sewn charge term is one
readout of the negative-lowered left words and the original right inputs. -/
theorem signed_diagonal_sewn_readout (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (N H K E : ℕ) (t dR dS : ℤ) (w : ℂ) (P Q R S : Oscillator D)
    (hP : P.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : Q.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hR : R.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) dR)
    (hS : S.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) dS)
    (ht : 2 * (t - (E : ℤ) + 1) = dR - dS)
    (hPb : ∀ j ∈ Finset.range (H - 1), modesBounded D N ((oscillatorLower D ^ j) P))
    (hQb : ∀ i ∈ Finset.range (K - 1), modesBounded D N ((oscillatorLower D ^ i) Q))
    (hRb : modesBounded D N R) (hSb : modesBounded D N S) :
    (-1 : ℂ) ^ (K : ℤ) * sewnReadout D q N w
      (boxedOscillator D N false false (loweringSum D (H - 1) P) *
        boxedOscillator D N false true (loweringSum D (K - 1) Q) *
        boxedOscillator D N true false R * boxedOscillator D N true true S) =
      projectOccupations D H K E t P Q R S (fun d g r s => sewnChargeTerm D d g r s q w) := by
  classical
  rw [project_occupations_on_signed_diagonal D hu H K E t dR dS P Q R S hP hQ hR hS ht]
  congr 1
  simp only [loweringSum, map_sum, map_smul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul]
  rw [sewnReadout_four D q N w _ _ _ _ (hPb j hj) (hQb i hi) hRb hSb]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun g _ =>
    Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

open private lowered_support_weight from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMProjectionModes

/-- Applying the negative lowering sum to the detector gives exactly the
original factorial sum of the selected sewn charge readouts. On each
detector summand the original signed diagonal is shifted by its lowering order. -/
theorem lowered_detector_sewn_readout (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (N H K L E C : ℕ) (m n r : ℤ) (w : ℂ) (P Q R S : Oscillator D)
    (hP : P.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : Q.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hR : R.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (L : ℤ) - 3))
    (hS : S.IsWeightedHomogeneous (fun i => (omega D i : ℤ))
      (2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3))
    (hPb : ∀ j ∈ Finset.range (H - 1), modesBounded D N ((oscillatorLower D ^ j) P))
    (hQb : ∀ i ∈ Finset.range (K - 1), modesBounded D N ((oscillatorLower D ^ i) Q))
    (hRb : modesBounded D N R)
    (hSb : ∀ ell ∈ Finset.range C, modesBounded D N ((oscillatorLower D ^ ell) S)) :
    (-1 : ℂ) ^ (K : ℤ) * sewnReadout D q N w
      (boxedOscillator D N false false (loweringSum D (H - 1) P) *
        boxedOscillator D N false true (loweringSum D (K - 1) Q) *
        boxedOscillator D N true false R *
        boxedOscillator D N true true (loweringSum D C S)) =
      ∑ ell ∈ Finset.range C, ((-1 : ℂ) ^ ell / (ell.factorial : ℂ)) *
        projectOccupations D H K E ((E : ℤ) + m + n + r + ell - H - K + 1)
          P Q R ((oscillatorLower D ^ ell) S) (fun d g r s => sewnChargeTerm D d g r s q w) := by
  classical
  have hsum : boxedOscillator D N true true (loweringSum D C S) =
      ∑ ell ∈ Finset.range C, ((-1 : ℂ) ^ ell / (ell.factorial : ℂ)) •
        boxedOscillator D N true true ((oscillatorLower D ^ ell) S) := by
    simp only [loweringSum, map_sum, map_smul]
  rw [hsum]
  simp only [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  let T := (oscillatorLower D ^ ell) S
  let d := 2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3 - 2 * (ell : ℤ)
  have hT : T.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) d := by
    intro i hi
    exact lowered_support_weight D hu S _ hS ell i (mem_support_iff.mpr hi)
  have h := signed_diagonal_sewn_readout D hu q N H K E
    ((E : ℤ) + m + n + r + ell - H - K + 1) (2 * (L : ℤ) - 3) d w P Q R T
    hP hQ hR hT (by dsimp [d]; ring) hPb hQb hRb (hSb ell hell)
  rw [← h]
  simp only [T, mul_smul_comm, map_smul, smul_eq_mul]
  ring

open OriginalFourMActualChart (loweringParameter)
open D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentFiniteLowering
  (wordPolynomial evaluate_lowering_word)
open D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport
  (exists_lowering_cutoff lowering_after_energy_cutoff)
open private evalLower from D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentFiniteLowering
open private wordScale from D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCauchyTaylor

private def creationWord (D : LatticeData) (xs : List (Index D)) : Oscillator D :=
  (xs.map MvPolynomial.X).prod

private theorem inverse_word_active (D : LatticeData) (hu : IsUnit D.G.det)
    (c : Chart) (x : ℝ) (s : Puncture) (xs : List (Index D)) (C : ℕ)
    (hs : loweringParameter c s = 1)
    (hC : ∀ j, C ≤ j → (oscillatorLower D ^ j) (creationWord D xs) = 0) :
    inverseLoweredWord D c x s xs = wordScale D c x s xs • loweringSum D C (creationWord D xs) := by
  rw [inverseLoweredWord, hs, evaluate_lowering_word D hu xs _ C hC]
  rfl

private theorem inverse_word_inactive (D : LatticeData) (hu : IsUnit D.G.det)
    (c : Chart) (x : ℝ) (s : Puncture) (xs : List (Index D))
    (hs : loweringParameter c s = 0) :
    inverseLoweredWord D c x s xs = wordScale D c x s xs • creationWord D xs := by
  classical
  obtain ⟨C, hC⟩ := exists_lowering_cutoff D hu (creationWord D xs)
  rw [inverseLoweredWord, hs, neg_zero,
    evaluate_lowering_word D hu xs 0 (C + 1) (fun j hj => hC j (by omega))]
  congr 1
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos C))]
  · simp [creationWord]
  · intro j _ hj
    simp [zero_pow hj]

private def chartDetectorCutoff (c : Chart) (H K L : ℕ) (m n r : ℤ) : ℕ :=
  match c with
  | .A => 1
  | .B | .D => ((H : ℤ) + K + L - m - n - r - 3).toNat

/-- The four actual inverse words evaluate to the original selected projector
on every signed diagonal, with the detector cutoff for its chart.
All coordinate scales multiply the original words before lowering. -/
theorem inverse_words_detector_projector (D : LatticeData) (hu : IsUnit D.G.det)
    (c : Chart) (x : ℝ) (q : Charge D)
    (N H K L E : ℕ) (m n r : ℤ) (w : ℂ) (words : Puncture → List (Index D))
    (hP : (creationWord D (words (firstLeft c))).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : (creationWord D (words (secondLeft c))).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hR : (creationWord D (words (firstRight c))).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (L : ℤ) - 3))
    (hS : (creationWord D (words .S)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3))
    (hPb : ∀ j ∈ Finset.range (H - 1), modesBounded D N
      ((oscillatorLower D ^ j) (creationWord D (words (firstLeft c)))))
    (hQb : ∀ j ∈ Finset.range (K - 1), modesBounded D N
      ((oscillatorLower D ^ j) (creationWord D (words (secondLeft c)))))
    (hRb : modesBounded D N (creationWord D (words (firstRight c))))
    (hSb : ∀ j ∈ Finset.range (chartDetectorCutoff c H K L m n r),
      modesBounded D N ((oscillatorLower D ^ j) (creationWord D (words .S)))) :
    let C := chartDetectorCutoff c H K L m n r
    let P := creationWord D (words (firstLeft c))
    let Q := creationWord D (words (secondLeft c))
    let R := creationWord D (words (firstRight c))
    let S := creationWord D (words .S)
    let W := fun s => inverseLoweredWord D c x s (words s)
    let scale := fun s => wordScale D c x s (words s)
    (-1 : ℂ) ^ (K : ℤ) * sewnReadout D q N w
      (boxedOscillator D N false false (W (firstLeft c)) *
        boxedOscillator D N false true (W (secondLeft c)) *
        boxedOscillator D N true false (W (firstRight c)) * boxedOscillator D N true true (W .S)) =
      (scale (firstLeft c) * scale (secondLeft c) * scale (firstRight c) * scale .S) *
        ∑ ell ∈ Finset.range C, ((-1 : ℂ) ^ ell / (ell.factorial : ℂ)) *
          projectOccupations D H K E ((E : ℤ) + m + n + r + ell - H - K + 1)
            P Q R ((oscillatorLower D ^ ell) S) (fun d g r s => sewnChargeTerm D d g r s q w) := by
  classical
  dsimp only
  have hp (j : ℕ) (hj : H - 1 ≤ j) :
      (oscillatorLower D ^ j) (creationWord D (words (firstLeft c))) = 0 := by
    apply lowering_after_energy_cutoff D hu _ _ hP
    omega
  have hq (j : ℕ) (hj : K - 1 ≤ j) :
      (oscillatorLower D ^ j) (creationWord D (words (secondLeft c))) = 0 := by
    apply lowering_after_energy_cutoff D hu _ _ hQ
    omega
  have hs (j : ℕ) (hj : ((H : ℤ) + K + L - m - n - r - 3).toNat ≤ j) :
      (oscillatorLower D ^ j) (creationWord D (words .S)) = 0 := by
    apply lowering_after_energy_cutoff D hu _ _ hS
    omega
  have hηP : loweringParameter c (firstLeft c) = 1 := by cases c <;> rfl
  have hηQ : loweringParameter c (secondLeft c) = 1 := by cases c <;> rfl
  have hηR : loweringParameter c (firstRight c) = 0 := by cases c <;> rfl
  have hWS : inverseLoweredWord D c x .S (words .S) =
      wordScale D c x .S (words .S) •
        loweringSum D (chartDetectorCutoff c H K L m n r) (creationWord D (words .S)) := by
    cases c with
    | A =>
      rw [inverse_word_inactive D hu _ _ _ _ rfl]
      simp [chartDetectorCutoff, loweringSum, Finset.range_one]
    | B => exact inverse_word_active D hu _ _ _ _ _ rfl hs
    | D => exact inverse_word_active D hu _ _ _ _ _ rfl hs
  rw [inverse_word_active D hu c x _ _ _ hηP hp, inverse_word_active D hu c x _ _ _ hηQ hq,
    inverse_word_inactive D hu c x _ _ hηR, hWS]
  simp only [map_smul, smul_mul_assoc, mul_smul_comm, smul_smul, smul_eq_mul]
  rw [← lowered_detector_sewn_readout D hu q N H K L E _ m n r w _ _ _ _
    hP hQ hR hS hPb hQb hRb hSb]
  ring

/-- On a radial chart the literal physical Taylor coefficient is the
convergent sum of the original signed projectors. The finite box bounds
both the inverse-transformed words and the individual lowering terms. -/
theorem radial_chart_signed_projector (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (h24 : D.rank = 24) (a : ModTwoCharge D)
    (N H K L E : ℕ) (m n r : ℤ) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (upperA : Bool) (c : Chart) (hc : c = .A ∨ c = .B) {w : ℂ} (hw : ‖w‖ < 1)
    (hwc : w ^ 2 = parameter c x)
    (hNome : Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x) = Q0 (w ^ 2))
    {X : Type*} [Fintype X] [DecidableEq X]
    (slot : X → Puncture) (mode : X → Index D) (bound : ∀ i, (mode i).2 ≤ N)
    (marks : Puncture → List X) (hslot : ∀ s j, j ∈ marks s → slot j = s)
    (hl : ((punctureWords marks).flatMap Prod.snd).Nodup)
    (hbox : ∀ s, modesBounded D N (inverseLoweredWord D c x s ((marks s).map mode)))
    (hsupp : ∀ s j, modesBounded D N
      ((oscillatorLower D ^ j) (creationWord D ((marks s).map mode))))
    (hP : (creationWord D ((marks (firstLeft c)).map mode)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : (creationWord D ((marks (secondLeft c)).map mode)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hR : (creationWord D ((marks (firstRight c)).map mode)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (L : ℤ) - 3))
    (hS : (creationWord D ((marks .S).map mode)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3)) :
    let words := fun s => (marks s).map mode
    let P := creationWord D (words (firstLeft c))
    let Q := creationWord D (words (secondLeft c))
    let R := creationWord D (words (firstRight c))
    let S := creationWord D (words .S)
    let l := (punctureWords marks).flatMap Prod.snd
    let scale := fun s => wordScale D c x s (words s)
    let scalar := (l.map fun i => relative c (slot i)).prod * (1 - w ^ 2) ^ (3 : ℕ) *
      (scale (firstLeft c) * scale (secondLeft c) * scale (firstRight c) * scale .S)
    HasSum (fun q : {q : Charge D // reduceCharge D q = a} =>
      scalar * ∑ ell ∈ Finset.range (chartDetectorCutoff c H K L m n r),
        ((-1 : ℂ) ^ ell / (ell.factorial : ℂ)) *
          projectOccupations D H K E ((E : ℤ) + m + n + r + ell - H - K + 1)
            P Q R ((oscillatorLower D ^ ell) S)
            (fun d g r s => sewnChargeTerm D d g r s q.val w))
      ((-1 : ℂ) ^ (K : ℤ) *
        spatialCoefficient (Sum.elim (fun i => (mode i).2) (fun _ => 1))
          (l.map Sum.inr ++ l.map Sum.inl) (fun z =>
            physicalProduct D hu slot (fun i => (mode i).1) upperA x c a
              (z ∘ Sum.inl) (z ∘ Sum.inr)) 0) := by
  dsimp only
  let words := fun s => (marks s).map mode
  let l := (punctureWords marks).flatMap Prod.snd
  let W := fun s => inverseLoweredWord D c x s (words s)
  let scalar := (l.map fun i => relative c (slot i)).prod * (1 - w ^ 2) ^ (3 : ℕ)
  have hs := (radial_sector_four_occupation D hu hD h24 a N hx hx₁ upperA c hc hw hwc hNome
    slot mode bound marks hslot hl hbox).mul_left ((-1 : ℂ) ^ (K : ℤ))
  refine hs.congr_fun ?_
  intro q
  have hp := inverse_words_detector_projector D hu c x q.val N H K L E m n r w words
    hP hQ hR hS (fun j _ => hsupp _ j) (fun j _ => hsupp _ j)
    (by simpa only [pow_zero, Module.End.one_apply] using hsupp (firstRight c) 0)
    (fun j _ => hsupp _ j)
  have h := sewnReadout_four D q.val N w (W (firstLeft c)) (W (secondLeft c))
    (W (firstRight c)) (W .S) (hbox _) (hbox _) (hbox _) (hbox _)
  dsimp only at hp
  rw [h] at hp
  linear_combination scalar * hp.symm

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSewnProjection
