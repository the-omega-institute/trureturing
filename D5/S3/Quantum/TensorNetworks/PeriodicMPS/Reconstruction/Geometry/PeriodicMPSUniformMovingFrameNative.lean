/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameNative
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameNative
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Native Pauli readout of moving-frame jets. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrame

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame

open Matrix MvPolynomial TrivSqZeroExt
open scoped Matrix Kronecker
open PeriodicMPSUniformAntisymmetricTransfer (BondMatrix TransferMatrix mixedRaw)
open PeriodicMPSUniformHardCoreTransferRecurrence (TwoBits)
open SevenSiteCriticalCertificate (observedRow rotationIndex sliceBlock)
open SevenSitePhysicalRankBridge (pauli_commutator_eq_rotationIndex)
open PeriodicMPSUniformNativeSliceReadout
  (alignedMoment rawSlicePolynomial alignedMoment_eq_transferPower)
open UniformNativeRotation (rotationPolynomial)
open UniformNativeCriticalMatrix (criticalMatrix)

open private pauli map_pauli from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalCertificate
open private alignedWord map_alignedWord map_pauliInsertionCoeff trace_pauli_mul_mixedRaw from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformNativeSliceReadout
open private certificate_pauli from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteReadoutDerivative

noncomputable section

def imaginary (R : Type*) [CommRing R] [Algebra ℂ R] : R := algebraMap ℂ R Complex.I

def half (R : Type*) [CommRing R] [Algebra ℂ R] : R := algebraMap ℂ R (1 / 2)

private theorem imaginary_sq (R : Type*) [CommRing R] [Algebra ℂ R] :
    imaginary R ^ 2 = -1 := by
  rw [imaginary, ← map_pow, Complex.I_sq, map_neg, map_one]

private theorem half_add (R : Type*) [CommRing R] [Algebra ℂ R] :
    half R + half R = 1 := by
  rw [half, ← map_add, show (1 / 2 + 1 / 2 : ℂ) = 1 by norm_num, map_one]

def pauliPair {R : Type*} [CommRing R] [Algebra ℂ R] (ab : Fin 4 × Fin 4) :
    TransferMatrix R := pauli (imaginary R) ab.1 ⊗ₖ pauli (imaginary R) ab.2

def pauliRead {R : Type*} [CommRing R] [Algebra ℂ R] (W : TransferMatrix R)
    (ab : Fin 4 × Fin 4) : R := (pauliPair ab * W).trace

/-- The two independent invariant triples give a point of the complexified
five-coordinate slice when their mixed traces agree. -/
def chartOf {R : Type*} [CommRing R] [Algebra ℂ R] (A B : Core R) : Fin 5 → R :=
  let d := (A 0).det
  let db := (B 0).det
  let e := (A 1).det
  let eb := (B 1).det
  let h := half R
  let i := imaginary R
  ![h * (d + db), mixedTrace A, h * (e + eb), -(i * h) * (d - db),
    -(i * h) * (e - eb)]

private theorem split_invariants {R : Type*} [CommRing R] [Algebra ℂ R] (u v : R) :
    half R * (u + v) + imaginary R * (-(imaginary R * half R) * (u - v)) = u ∧
    half R * (u + v) + -imaginary R * (-(imaginary R * half R) * (u - v)) = v := by
  have hh := half_add R
  have hi := imaginary_sq R
  constructor
  · linear_combination u * hh - half R * (u - v) * hi
  · linear_combination v * hh + half R * (u - v) * hi

/-- Evaluate the native raw polynomial over any complex algebra, including
dual numbers and algebraic extensions of the divisor function field. -/
theorem rawSlice_eq_pauliRead {R : Type*} [CommRing R] [Algebra ℂ R]
    (m : ℕ) (A B : Core R) (ha : traces A = ![1, 0]) (hb : traces B = ![1, 0])
    (hk : mixedTrace A = mixedTrace B) (ab : Fin 4 × Fin 4) :
    aeval (chartOf A B) (rawSlicePolynomial m ab) = pauliRead (mixedRaw A B m) ab := by
  let z := chartOf A B
  let f : MvPolynomial (Fin 5) ℂ →+* R := (aeval z).toRingHom
  have h (b : Bool) :
      f ∘ sliceBlock (C Complex.I) (X : Fin 5 → MvPolynomial (Fin 5) ℂ) b = sliceBlock (imaginary R) z b := by
    funext i
    cases b <;> fin_cases i <;> simp [f, sliceBlock, Function.comp_apply, imaginary]
  have hA : sliceBlock (imaginary R) z true =
      ![(A 0).det, mixedTrace A, (A 1).det] := by
    funext i
    fin_cases i
    · exact (split_invariants (A 0).det (B 0).det).1
    · rfl
    · exact (split_invariants (A 1).det (B 1).det).1
  have hB : sliceBlock (imaginary R) z false =
      ![(B 0).det, mixedTrace B, (B 1).det] := by
    funext i
    fin_cases i
    · exact (split_invariants (A 0).det (B 0).det).2
    · exact hk
    · exact (split_invariants (A 1).det (B 1).det).2
  change f (rawSlicePolynomial m ab) = _
  have hi : f (C Complex.I) = imaginary R := aeval_C z Complex.I
  simp only [rawSlicePolynomial, alignedMoment, map_sum, map_mul, map_pauliInsertionCoeff,
    map_alignedWord, h, hi, hA, hB]
  change alignedMoment m (imaginary R) ![(A 0).det, mixedTrace A, (A 1).det]
    ![(B 0).det, mixedTrace B, (B 1).det] ab = pauliRead (mixedRaw A B m) ab
  exact (alignedMoment_eq_transferPower m (imaginary R) A B
    (congrFun ha 0) (congrFun ha 1) (congrFun hb 0) (congrFun hb 1) ab).trans
      (trace_pauli_mul_mixedRaw m (imaginary R) A B ab).symm


section Jets

variable {E : Type*} [Field E] [Algebra ℂ E]

local notation "D" => DualNumber E

private theorem fst_aeval {ι : Type*} (z : ι → D) (p : MvPolynomial ι ℂ) :
    (aeval z p).fst = aeval (fun j => (z j).fst) p := by
  let f : D →ₐ[ℂ] E := (fstHom E E E).restrictScalars ℂ
  change (f.comp (aeval z)) p = _
  congr 1
  apply MvPolynomial.algHom_ext
  intro j
  simp [f]

/-- An arbitrary dual-number coordinate direction contracts all coordinate
partials of the native polynomial with its actual tangent speeds. -/
theorem snd_aeval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → D) (p : MvPolynomial ι ℂ) :
    (aeval z p).snd = ∑ j, (z j).snd * aeval (fun i => (z i).fst) (pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : algebraMap ℂ D a = inl (algebraMap ℂ E a) :=
      (IsScalarTower.algebraMap_apply ℂ E D a)
    simp [h]
  | add p q hp hq =>
    simp only [map_add, snd_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p i hp =>
    simp only [map_mul, DualNumber.snd_mul, aeval_X, fst_aeval, hp, pderiv_mul, pderiv_X,
      map_add, mul_add, Finset.sum_add_distrib, map_mul]
    rw [add_comm, Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      ring
    · rw [Finset.sum_eq_single i]
      · simp [mul_comm]
      · intro j _ hj
        simp [Ne.symm hj]
      · simp

private theorem imaginary_dual : imaginary D = inl (imaginary E) :=
  IsScalarTower.algebraMap_apply ℂ E D _

private theorem pauliPair_dual (ab : Fin 4 × Fin 4) :
    (pauliPair ab : TransferMatrix D) =
      (pauliPair ab : TransferMatrix E).map (inlHom E E) := by
  apply Matrix.ext
  intro i j
  simp only [pauliPair, imaginary_dual, Matrix.map_apply, Matrix.kroneckerMap_apply,
    ← inlHom_apply, ← map_pauli, ← map_mul]

private theorem pauliRead_jet (W : TransferMatrix D) (ab : Fin 4 × Fin 4) :
    (pauliRead W ab).fst = pauliRead (jetValue W) ab ∧
      (pauliRead W ab).snd = pauliRead (jetTangent W) ab := by
  simp [pauliRead, pauliPair_dual, Matrix.trace, Matrix.mul_apply, jetValue, jetTangent,
    fst_sum, snd_sum]

theorem aligned_raw_jet (m : ℕ) (A B : Core D) (ha : traces A = ![1, 0])
    (hb : traces B = ![1, 0]) (hk : mixedTrace A = mixedTrace B)
    (ab : Fin 4 × Fin 4) :
    let z := chartOf A B
    let x := fun i => (z i).fst
    let W := mixedRaw A B m
    pauliRead (jetValue W) ab = aeval x (rawSlicePolynomial m ab) ∧
      pauliRead (jetTangent W) ab =
        ∑ j, (z j).snd * aeval x (pderiv j (rawSlicePolynomial m ab)) := by
  simp only
  have h := rawSlice_eq_pauliRead m A B ha hb hk ab
  rw [← (pauliRead_jet _ _).1, ← (pauliRead_jet _ _).2, ← h, fst_aeval, snd_aeval]
  exact ⟨rfl, rfl⟩

/-- The signs agree with the native X, Y, Z rotation columns. -/
def rotationGenerator (j : Fin 3) : BondMatrix E :=
  (-(imaginary E * half E)) • pauli (imaginary E) j.succ

private theorem pauli_commutator (j : Fin 3) (a : Fin 4) :
    pauli (imaginary E) a * rotationGenerator j - rotationGenerator j * pauli (imaginary E) a =
      ((rotationIndex j a).1 : E) • pauli (imaginary E) (rotationIndex j a).2 := by
  have h : pauli Complex.I a * ((- (Complex.I * (1 / 2))) • pauli Complex.I j.succ) -
      ((- (Complex.I * (1 / 2))) • pauli Complex.I j.succ) * pauli Complex.I a =
      ((rotationIndex j a).1 : ℂ) • pauli Complex.I (rotationIndex j a).2 := by
    simp only [certificate_pauli, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
    rw [← pauli_commutator_eq_rotationIndex]
    rw [show Complex.I / 2 = Complex.I * (1 / 2) by ring, neg_smul, ← smul_neg, neg_sub]
  let f := algebraMap ℂ E
  have hmap (a : Fin 4) : f.mapMatrix (pauli Complex.I a) = pauli (imaginary E) a := by
    apply Matrix.ext
    intro u v
    exact map_pauli f Complex.I a u v
  have hsmul (c : ℂ) (M : BondMatrix ℂ) :
      f.mapMatrix (c • M) = f c • f.mapMatrix M := by
    apply Matrix.ext
    intro u v
    exact f.map_mul c (M u v)
  have he := congrArg f.mapMatrix h
  simp only [map_sub, map_mul, hsmul, map_neg, map_intCast, hmap] at he
  exact he

omit [Algebra ℂ E] in
private theorem pair_commutator (A B H : BondMatrix E) :
    (A ⊗ₖ B) * pairGenerator H - pairGenerator H * (A ⊗ₖ B) =
      (A * H - H * A) ⊗ₖ B + A ⊗ₖ (B * H - H * B) := by
  simp only [pairGenerator, mul_add, add_mul, ← Matrix.mul_kronecker_mul, mul_one, one_mul]
  apply Matrix.ext
  intro i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.kroneckerMap_apply, sub_mul, mul_sub]
  ring

theorem pauliRead_rotation (j : Fin 3) (W : TransferMatrix E) (ab : Fin 4 × Fin 4) :
    pauliRead (physicalTangent (rotationGenerator j) W) ab =
      ((rotationIndex j ab.1).1 : E) * pauliRead W ((rotationIndex j ab.1).2, ab.2) +
      ((rotationIndex j ab.2).1 : E) * pauliRead W (ab.1, (rotationIndex j ab.2).2) := by
  let O : TransferMatrix E := pauliPair ab
  let H : TransferMatrix E := pairGenerator (rotationGenerator j)
  have htr : (O * (H * W - W * H)).trace = ((O * H - H * O) * W).trace := by
    simp only [mul_sub, sub_mul, Matrix.trace_sub, ← mul_assoc O H, ← mul_assoc O W]
    rw [Matrix.trace_mul_cycle O W H, mul_assoc H O]
  change (O * (H * W - W * H)).trace = _
  rw [htr]
  dsimp only [O, H, pauliPair]
  rw [pair_commutator, pauli_commutator, pauli_commutator, smul_kronecker,
    kronecker_smul, add_mul, Matrix.trace_add, smul_mul_assoc, smul_mul_assoc,
    Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  rfl

def rotationCoefficients (H : BondMatrix E) : Fin 3 → E :=
  ![imaginary E * (H 0 1 + H 1 0), H 1 0 - H 0 1, imaginary E * (H 0 0 - H 1 1)]

private theorem decompose_generator (H : BondMatrix E) :
    H = (half E * H.trace) • 1 + ∑ j, rotationCoefficients H j • rotationGenerator j := by
  have hh := half_add E
  have hi := imaginary_sq E
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationCoefficients, rotationGenerator, pauli, Fin.sum_univ_three, Matrix.trace,
      Fin.sum_univ_two, smul_eq_mul]
  · linear_combination -(H 0 0) * hh + half E * (H 0 0 - H 1 1) * hi
  · linear_combination -(H 0 1) * hh + 2 * H 0 1 * half E * hi
  · linear_combination -(H 1 0) * hh + 2 * H 1 0 * half E * hi
  · linear_combination -(H 1 1) * hh - half E * (H 0 0 - H 1 1) * hi

private def physicalTangentLinear (W : TransferMatrix E) : BondMatrix E →ₗ[E] TransferMatrix E where
  toFun H := physicalTangent H W
  map_add' H J := by
    have h : pairGenerator (H + J) = pairGenerator H + pairGenerator J := by
      apply Matrix.ext
      intro i j
      simp [pairGenerator, Matrix.kroneckerMap_apply, add_mul, mul_add]
      abel
    simp only [physicalTangent, h, add_mul, mul_add]
    abel
  map_smul' c H := by
    have h : pairGenerator (c • H) = c • pairGenerator H := by
      apply Matrix.ext
      intro i j
      simp [pairGenerator, Matrix.kroneckerMap_apply, mul_assoc, mul_left_comm, mul_add]
    simp [physicalTangent, h, smul_sub]

private def pauliReadLinear (ab : Fin 4 × Fin 4) : TransferMatrix E →ₗ[E] E where
  toFun W := pauliRead W ab
  map_add' A B := by simp [pauliRead, mul_add, Matrix.trace_add]
  map_smul' c A := by simp [pauliRead, Matrix.trace_smul]

omit [Algebra ℂ E] in
private theorem physicalTangent_scalar (c : E) (W : TransferMatrix E) :
    physicalTangent (c • 1) W = 0 := by
  simp [physicalTangent, pairGenerator, smul_kronecker, kronecker_smul,
    add_mul, mul_add]

theorem pauliRead_physicalTangent (H : BondMatrix E) (W : TransferMatrix E)
    (ab : Fin 4 × Fin 4) :
    pauliRead (physicalTangent H W) ab =
      ∑ j, rotationCoefficients H j * pauliRead (physicalTangent (rotationGenerator j) W) ab := by
  let F := (pauliReadLinear ab).comp (physicalTangentLinear W)
  have hz : F ((half E * H.trace) • 1) = 0 := by
    change pauliRead (physicalTangent ((half E * H.trace) • 1) W) ab = 0
    rw [physicalTangent_scalar]
    simp [pauliRead]
  change F H = ∑ j, rotationCoefficients H j * F (rotationGenerator j)
  conv_lhs => rw [decompose_generator H]
  simp [hz, map_sum]

private theorem rotation_eq_eval (m : ℕ) (x : Fin 5 → E) (W : TransferMatrix E)
    (hW : ∀ ab, pauliRead W ab = aeval x (rawSlicePolynomial m ab))
    (j : Fin 3) (ab : Fin 4 × Fin 4) :
    pauliRead (physicalTangent (rotationGenerator j) W) ab =
      aeval x (rotationPolynomial m j ab) := by
  rw [pauliRead_rotation, hW, hW]
  simp [rotationPolynomial]

/-- The native augmented matrix gives the transported raw value and every
transported raw first jet at the literal residual power `m`. The five
speeds come from the moving invariant coordinates and the three rotation
speeds from the right logarithmic derivative of its physical frame. -/
theorem native_movingFrame_comparison (m : ℕ) (A B : Core D) (g h : BondMatrix D)
    (hhg : h * g = 1) (hgh : g * h = 1)
    (ha : traces (mix g A) = ![1, 0]) (hb : traces (mix hᵀ B) = ![1, 0])
    (hk : mixedTrace (mix g A) = mixedTrace (mix hᵀ B)) :
    let z := chartOf (mix g A) (mix hᵀ B)
    let x := fun i => (z i).fst
    let W := mixedRaw A B m
    let L := pairFrame (jetValue g)
    let R := pairFrame (jetValue h)
    let c := rotationCoefficients (jetTangent g * jetValue h)
    let N := (criticalMatrix m).map (aeval x)
    ∀ i : Fin 10,
      pauliRead (L * jetValue W * R) (observedRow i) = N i 5 ∧
      pauliRead (L * jetTangent W * R) (observedRow i) =
        ∑ j : Fin 5, (z j).snd * N i (Fin.castLE (by decide) j) -
        ∑ j : Fin 3, c j * N i (Fin.natAdd 6 j) := by
  dsimp only
  let z := chartOf (mix g A) (mix hᵀ B)
  let x := fun i => (z i).fst
  let W := mixedRaw (mix g A) (mix hᵀ B) m
  intro i
  have hjet (ab : Fin 4 × Fin 4) := aligned_raw_jet m _ _ ha hb hk ab
  have hW (ab : Fin 4 × Fin 4) : pauliRead (jetValue W) ab =
      aeval x (rawSlicePolynomial m ab) := (hjet ab).1
  have hrot (j : Fin 3) : ((criticalMatrix m).map (aeval x)) i (Fin.natAdd 6 j) =
      aeval x (rotationPolynomial m j (observedRow i)) := by
    fin_cases j <;> rfl
  have hpart (j : Fin 5) : ((criticalMatrix m).map (aeval x)) i (Fin.castLE (by decide) j) =
      aeval x (pderiv j (rawSlicePolynomial m (observedRow i))) := by
    simp [Matrix.map_apply, criticalMatrix, j.isLt]
  change _ = ((criticalMatrix m).map (aeval x)) i 5 ∧ _
  constructor
  · rw [← mixedRaw_movingFrame_radial g h hhg]
    simpa [Matrix.map_apply, criticalMatrix] using hW (observedRow i)
  · rw [mixedRaw_movingFrame_jet g h hhg hgh]
    change pauliRead (jetTangent W - _) (observedRow i) = _
    have hsub := (pauliReadLinear (E := E) (observedRow i)).map_sub
      (jetTangent W) (physicalTangent (jetTangent g * jetValue h) (jetValue W))
    change pauliRead (jetTangent W - _) (observedRow i) =
      pauliRead (jetTangent W) (observedRow i) - pauliRead _ (observedRow i) at hsub
    rw [hsub, (hjet (observedRow i)).2, pauliRead_physicalTangent]
    change _ = (∑ j : Fin 5, (z j).snd * ((criticalMatrix m).map (aeval x)) i
      (Fin.castLE (by decide) j)) - ∑ j : Fin 3,
        rotationCoefficients (jetTangent g * jetValue h) j *
          ((criticalMatrix m).map (aeval x)) i (Fin.natAdd 6 j)
    simp_rw [hpart, hrot, rotation_eq_eval m x _ hW]
    rfl

end Jets

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame
