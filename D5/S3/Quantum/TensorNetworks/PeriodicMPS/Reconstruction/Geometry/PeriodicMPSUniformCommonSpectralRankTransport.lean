/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformCommonSpectralRankTransport
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformCommonSpectralRankTransport
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Specialized trace-word rank transfers to the generic determinant chart. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformSpecialSpectralDomains
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteTraceBase
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformCommonSpectralRankTransport

open Matrix MvPolynomial TrivSqZeroExt
open PeriodicMPSCommonSpectralJets
open PeriodicMPSUniformSpecialSpectralDomains (balancedWitnessCore balancedWitnessCore_data witnessK)
open SevenSiteTraceBase (wordPolynomial wordPolynomial_eq_trace wordProduct)
open private form map_form wordProduct_smul from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteTraceBase

noncomputable section

abbrev Coordinate := Fin 2 × Fin 5

/-- The two independent trace blocks have order `(tr A, tr B, det A, det B, tr AB)`. -/
def invariants {R : Type*} [CommRing R] (A : Fin 2 → Core R) : Fin 5 → R :=
  ![(A 0).trace, (A 1).trace, (A 0).det, (A 1).det, (A 0 * A 1).trace]

def coordinates {R : Type*} [CommRing R] (K B : Fin 2 → Core R) : Coordinate → R :=
  fun i => if i.1 = 0 then invariants K i.2 else invariants B i.2

def gramChart {R : Type*} [CommRing R] (m : ℕ) (p : Coordinate → R) (ab : Entry) : R :=
  let word (b : Fin 2) (q : Bits) (w : Fin m → Fin 2) :=
    wordPolynomial (p (b, 0)) (p (b, 1)) (p (b, 2)) (p (b, 3)) (p (b, 4))
      (List.ofFn (Fin.append ![q.1, q.2] w))
  ∑ w : Fin m → Fin 2, word 0 ab.1 w * word 1 ab.2 w

private theorem wordReadout_eq (R : Type*) [CommRing R] (A : Fin 2 → Core R)
    (q : Bits) {m : ℕ} (w : Fin m → Fin 2) :
    wordReadout A q w = (wordProduct A (Fin.append ![q.1, q.2] w)).trace := by
  unfold wordProduct wordReadout suffixProduct
  rw [List.ofFn_comp' (Fin.append ![q.1, q.2] w) A, List.ofFn_fin_append,
    List.map_append, List.prod_append, List.map_ofFn]
  simp [List.ofFn_succ, Function.comp_def]

/-- The literal adjacent-pair contraction factors over any commutative ring, including dual numbers. -/
theorem literalGram_eq_chart {R : Type*} [CommRing R] (K B : Fin 2 → Core R)
    (m : ℕ) (ab : Entry) : literalGram K B m ab = gramChart m (coordinates K B) ab := by
  classical
  unfold literalGram gramChart
  apply Finset.sum_congr rfl
  intro w _
  rw [wordReadout_eq, wordReadout_eq, ← wordPolynomial_eq_trace, ← wordPolynomial_eq_trace]
  simp [coordinates, invariants]

private theorem map_wordPolynomial {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t s d e k : R) (w : List (Fin 2)) :
    f (wordPolynomial t s d e k w) = wordPolynomial (f t) (f s) (f d) (f e) (f k) w := by
  unfold wordPolynomial
  rw [map_form]
  obtain ⟨u, a, b, c⟩ := form t s d e k w
  simp [map_ofNat]

theorem map_gramChart {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (m : ℕ) (p : Coordinate → R) (ab : Entry) :
    f (gramChart m p ab) = gramChart m (f ∘ p) ab := by
  simp only [gramChart, map_sum, map_mul, map_wordPolynomial, Function.comp_apply]

private theorem map_invariants {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Fin 2 → Core R) :
    f ∘ invariants A = invariants (fun i => (A i).map f) := by
  funext i
  fin_cases i <;> simp [invariants, AddMonoidHom.map_trace, RingHom.map_det]

theorem map_coordinates {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (K B : Fin 2 → Core R) :
    f ∘ coordinates K B = coordinates (fun i => (K i).map f) (fun i => (B i).map f) := by
  funext i
  by_cases hi : i.1 = 0
  · simp only [Function.comp_apply, coordinates, ite_eq_left hi]
    exact congrFun (map_invariants f K) i.2
  · simp only [Function.comp_apply, coordinates, ite_eq_right hi]
    exact congrFun (map_invariants f B) i.2

private theorem wordReadout_smul {R : Type*} [CommRing R] (A : Fin 2 → Core R)
    (c : Fin 2 → R) (q : Bits) {m : ℕ} (w : Fin m → Fin 2) :
    wordReadout (fun i => c i • A i) q w =
      (c q.1 * c q.2 * (List.ofFn fun j => c (w j)).prod) * wordReadout A q w := by
  rw [wordReadout_eq, wordReadout_eq, wordProduct_smul, Matrix.trace_smul, smul_eq_mul]
  rw [List.ofFn_comp' (Fin.append ![q.1, q.2] w) c, List.ofFn_fin_append,
    List.map_append, List.prod_append, List.map_ofFn]
  simp [List.ofFn_succ, Function.comp_def, mul_assoc]

/-- Opposite label scalings cancel on the common suffix. Only the two exposed
ket labels and two exposed bra labels contribute to the Gram row multiplier. -/
theorem literalGram_balance {R : Type*} [CommRing R] (K B : Fin 2 → Core R)
    (c f : Fin 2 → R) (hc : ∀ i, c i * f i = 1) (m : ℕ) (ab : Entry) :
    literalGram (fun i => c i • K i) (fun i => f i • B i) m ab =
      (c ab.1.1 * c ab.1.2 * (f ab.2.1 * f ab.2.2)) * literalGram K B m ab := by
  classical
  have hprod {n : ℕ} (w : Fin n → Fin 2) :
      (List.ofFn fun j => c (w j)).prod * (List.ofFn fun j => f (w j)).prod = 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [List.ofFn_succ, List.prod_cons]
      rw [mul_mul_mul_comm, hc, ih, mul_one]
  simp only [literalGram, Finset.mul_sum, wordReadout_smul]
  apply Finset.sum_congr rfl
  intro w _
  calc
    _ = (c ab.1.1 * c ab.1.2 * (f ab.2.1 * f ab.2.2)) *
        ((List.ofFn fun j => c (w j)).prod * (List.ofFn fun j => f (w j)).prod) *
        (wordReadout K ab.1 w * wordReadout B ab.2 w) := by ac_rfl
    _ = _ := by rw [hprod, mul_one]

/-- Scaling whole blocks gives the radial direction and the opposite scalar gauge. -/
theorem literalGram_blockScale {R : Type*} [CommRing R] (K B : Fin 2 → Core R)
    (c f : R) (m : ℕ) (ab : Entry) :
    literalGram (fun i => c • K i) (fun i => f • B i) m ab =
      (c * f) ^ (2 + m) * literalGram K B m ab := by
  classical
  simp only [literalGram, Finset.mul_sum, wordReadout_smul]
  apply Finset.sum_congr rfl
  intro w _
  simp [List.ofFn_const, List.prod_replicate, mul_pow, pow_add, pow_two]
  ac_rfl

private def fstRing (R : Type*) [CommRing R] : DualNumber R →+* R :=
  (fstHom R R R).toRingHom

private def dual {R : Type*} (a b : R) : DualNumber R := (a, b)

@[simp] private theorem fst_dual {R : Type*} (a b : R) : (dual a b).fst = a := rfl
@[simp] private theorem snd_dual {R : Type*} (a b : R) : (dual a b).snd = b := rfl

private def dualMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    DualNumber R →+* DualNumber S where
  toFun x := dual (f x.fst) (f x.snd)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · exact f.map_add x.fst y.fst
    · exact f.map_add x.snd y.snd
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · exact f.map_mul x.fst y.fst
    · simp only [DualNumber.snd_mul, map_add, map_mul, fst_dual, snd_dual]

private def jetEval {R : Type*} [CommRing R] {ι : Type*} (x v : ι → R) :
    MvPolynomial ι R →+* DualNumber R :=
  eval₂Hom (inlHom R R) fun i => dual (x i) (v i)

@[simp] private theorem jetEval_C {R : Type*} [CommRing R] {ι : Type*}
    (x v : ι → R) (a : R) : jetEval x v (C a) = inlHom R R a :=
  eval₂Hom_C _ _ _

@[simp] private theorem jetEval_X {R : Type*} [CommRing R] {ι : Type*}
    (x v : ι → R) (i : ι) : jetEval x v (X i) = dual (x i) (v i) :=
  eval₂Hom_X' _ _ _

private theorem fst_jetEval {R : Type*} [CommRing R] {ι : Type*}
    (x v : ι → R) (p : MvPolynomial ι R) :
    (jetEval x v p).fst = eval x p := by
  have h : (fstRing R).comp (jetEval x v) = eval x := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
      rfl
    · intro i
      simp
      rfl
  exact DFunLike.congr_fun h p

/-- Coefficient of the dual-number variable in multivariate polynomial evaluation. -/
def jetDifferential {R : Type*} [CommRing R] {ι : Type*} (x : ι → R)
    (p : MvPolynomial ι R) : (ι → R) →ₗ[R] R where
  toFun v := (jetEval x v p).snd
  map_add' v w := by
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq, add_add_add_comm]
    | mul_X p i hp =>
      simp only [map_mul, DualNumber.snd_mul, fst_jetEval, jetEval_X, fst_dual, snd_dual, hp, Pi.add_apply]
      ring
  map_smul' c v := by
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq, mul_add]
    | mul_X p i hp =>
      simp only [map_mul, DualNumber.snd_mul, fst_jetEval, jetEval_X, fst_dual, snd_dual, hp,
        Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
      ring

/-- The differential of the exact ten-invariant chart, with all exposed Gram entries. -/
def gramDifferential {R : Type*} [CommRing R] (m : ℕ) (x : Coordinate → R) :
    (Coordinate → R) →ₗ[R] (Entry → R) :=
  LinearMap.pi fun ab => jetDifferential x (gramChart m X ab)

theorem gramDifferential_apply {R : Type*} [CommRing R] (m : ℕ) (x v : Coordinate → R)
    (ab : Entry) :
    gramDifferential m x v ab = TrivSqZeroExt.snd (gramChart m (fun i => dual (x i) (v i)) ab) := by
  change (jetEval x v (gramChart m X ab)).snd = _
  rw [map_gramChart]
  simp [Function.comp_def]

/-- The exact independent ket and bra invariant coordinates of the balanced cores. -/
def witnessCoordinates : Coordinate → ℝ :=
  coordinates (balancedWitnessCore ∘ ketIndex) (balancedWitnessCore ∘ braIndex)

theorem witnessCoordinates_eq :
    witnessCoordinates = (fun i : Coordinate =>
      if i.1 = 0 then (![1, 0, 1, 0, (witnessK : ℝ)] : Fin 5 → ℝ) i.2
      else (![1, 0, 3, -2, (witnessK : ℝ)] : Fin 5 → ℝ) i.2) := by
  obtain ⟨hd, hdb, he, heb, hk, hkb⟩ := balancedWitnessCore_data
  have htr (i : Fin 4) : (balancedWitnessCore i).trace = (![1, 0, 1, 0] : Fin 4 → ℝ) i := by
    fin_cases i <;> norm_num [balancedWitnessCore, cores, Matrix.trace_fin_two, Matrix.smul_apply]
  funext i
  rcases i with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [witnessCoordinates, coordinates, invariants, show ketIndex 0 = 0 from rfl,
      show ketIndex 1 = 1 from rfl, show braIndex 0 = 2 from rfl, show braIndex 1 = 3 from rfl,
      htr, hd, hdb, he, heb, hk, hkb]

private def balanceKet : Fin 2 → ℝ := ![1, -(witnessK : ℝ)]
private def balanceBra : Fin 2 → ℝ := ![1, (-(witnessK : ℝ))⁻¹]

private theorem balance_product (i : Fin 2) : balanceKet i * balanceBra i = 1 := by
  fin_cases i <;> simp [balanceKet, balanceBra, Units.ne_zero witnessK]

private def balancedKetJet (d : Direction) (i : Fin 2) : Core (DualNumber ℝ) :=
  inlHom ℝ ℝ (balanceKet i) • (jetCore d (ketIndex i)).map (dualMap (Rat.castHom ℝ))

private def balancedBraJet (d : Direction) (i : Fin 2) : Core (DualNumber ℝ) :=
  inlHom ℝ ℝ (balanceBra i) • (jetCore d (braIndex i)).map (dualMap (Rat.castHom ℝ))

private theorem fst_balancedKetJet (d : Direction) (i : Fin 2) :
    (balancedKetJet d i).map (fstRing ℝ) = balancedWitnessCore (ketIndex i) := by
  fin_cases i <;> rfl

private theorem fst_balancedBraJet (d : Direction) (i : Fin 2) :
    (balancedBraJet d i).map (fstRing ℝ) = balancedWitnessCore (braIndex i) := by
  fin_cases i <;> rfl

private def witnessDirection (d : Direction) (i : Coordinate) : ℝ :=
  (coordinates (balancedKetJet d) (balancedBraJet d) i).snd

private def rowFactor (ab : Entry) : ℝ :=
  balanceKet ab.1.1 * balanceKet ab.1.2 * (balanceBra ab.2.1 * balanceBra ab.2.2)

private theorem rowFactor_ne_zero (ab : Entry) : rowFactor ab ≠ 0 := by
  have hk (i : Fin 2) : balanceKet i ≠ 0 := (mul_ne_zero_iff.mp
    (show balanceKet i * balanceBra i ≠ 0 by rw [balance_product]; exact one_ne_zero)).1
  have hb (i : Fin 2) : balanceBra i ≠ 0 := (mul_ne_zero_iff.mp
    (show balanceKet i * balanceBra i ≠ 0 by rw [balance_product]; exact one_ne_zero)).2
  exact mul_ne_zero (mul_ne_zero (hk _) (hk _)) (mul_ne_zero (hb _) (hb _))

private theorem map_literalGram {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (K B : Fin 2 → Core R) (m : ℕ) (ab : Entry) :
    f (literalGram K B m ab) =
      literalGram (fun i => (K i).map f) (fun i => (B i).map f) m ab := by
  simp only [literalGram_eq_chart, map_gramChart, map_coordinates]

/-- A certificate direction after balancing, including its exact exposed-row multiplier. -/
theorem gramDifferential_witness_entry (m : ℕ) (i j : Fin 9) :
    gramDifferential m witnessCoordinates (witnessDirection (columns j)) (rows i) =
      rowFactor (rows i) * ((literalJacobian m i j : ℚ) : ℝ) := by
  let d := columns j
  have heq : (fun a => dual (witnessCoordinates a) (witnessDirection d a)) =
      coordinates (balancedKetJet d) (balancedBraJet d) := by
    funext a
    apply TrivSqZeroExt.ext
    · have h := congrFun (map_coordinates (fstRing ℝ) (balancedKetJet d) (balancedBraJet d)) a
      change (coordinates (balancedKetJet d) (balancedBraJet d) a).fst =
        coordinates (fun i => (balancedKetJet d i).map (fstRing ℝ))
          (fun i => (balancedBraJet d i).map (fstRing ℝ)) a at h
      simpa only [witnessCoordinates, fst_balancedKetJet, fst_balancedBraJet, Function.comp_def,
        fst_dual] using h.symm
    · rfl
  rw [gramDifferential_apply, heq]
  change (gramChart m (coordinates (balancedKetJet d) (balancedBraJet d)) (rows i)).snd = _
  rw [← literalGram_eq_chart]
  let K := jetCore d ∘ ketIndex
  let B := jetCore d ∘ braIndex
  let f := dualMap (Rat.castHom ℝ)
  let c := inlHom ℝ ℝ
  change (literalGram (fun a => c (balanceKet a) • (K a).map f)
    (fun a => c (balanceBra a) • (B a).map f) m (rows i)).snd =
      rowFactor (rows i) * (Rat.castHom ℝ) (literalJacobian m i j)
  have hbal (a : Fin 2) : c (balanceKet a) * c (balanceBra a) = 1 := by
    rw [← c.map_mul, balance_product, c.map_one]
  rw [literalGram_balance _ _ _ _ hbal]
  rw [← map_literalGram f K B, ← c.map_mul, ← c.map_mul, ← c.map_mul]
  change (c (rowFactor (rows i)) * f (literalGram K B m (rows i))).snd = _
  simp only [DualNumber.snd_mul, c, inlHom_apply, fst_inl, snd_inl, zero_mul, add_zero]
  change rowFactor (rows i) * (Rat.castHom ℝ) (literalGram K B m (rows i)).snd = _
  rw [literalJacobian_eq_J, literalGram_eq_contraction]
  rfl

def witnessGramMinor (m : ℕ) : Matrix (Fin 9) (Fin 9) ℝ :=
  fun i j => gramDifferential m witnessCoordinates (witnessDirection (columns j)) (rows i)

/-- This minor belongs to the invariant Gram differential evaluated on the
images of the certificate directions. -/
theorem witnessGramMinor_det_ne_zero {m : ℕ} (hm : 5 ≤ m) :
    (witnessGramMinor m).det ≠ 0 := by
  have heq : witnessGramMinor m =
      diagonal (rowFactor ∘ rows) * (literalJacobian m).map (Rat.castHom ℝ) := by
    apply Matrix.ext
    intro i j
    rw [Matrix.diagonal_mul]
    exact gramDifferential_witness_entry m i j
  rw [heq, Matrix.det_mul, Matrix.det_diagonal]
  change _ * ((Rat.castHom ℝ).mapMatrix (literalJacobian m)).det ≠ 0
  rw [← (Rat.castHom ℝ).map_det]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => rowFactor_ne_zero (rows i))
    (Rat.cast_ne_zero.mpr (PeriodicMPSCommonSpectralDeterminant.literalJacobian_det_ne_zero hm))

/-- The certificate supplies nine independent output directions in the invariant chart. -/
theorem nine_le_gramDifferential_rank {m : ℕ} (hm : 5 ≤ m) :
    9 ≤ Module.finrank ℝ (LinearMap.range (gramDifferential m witnessCoordinates)) := by
  let D := gramDifferential m witnessCoordinates
  let directions := Fintype.linearCombination ℝ (witnessDirection ∘ columns)
  let extract : (Entry → ℝ) →ₗ[ℝ] (Fin 9 → ℝ) := LinearMap.pi fun i => LinearMap.proj (rows i)
  have heq : (witnessGramMinor m).mulVecLin = extract.comp (D.comp directions) := by
    apply LinearMap.ext
    intro v
    funext i
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, witnessGramMinor, D, directions,
      extract, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply,
      Fintype.linearCombination_apply, Function.comp_apply, map_sum, map_smul,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  calc
    9 = (witnessGramMinor m).rank := by
      rw [Matrix.rank_of_det_ne_zero (witnessGramMinor_det_ne_zero hm), Fintype.card_fin]
    _ = Module.finrank ℝ (LinearMap.range (extract.comp (D.comp directions))) := by rw [Matrix.rank, heq]
    _ ≤ Module.finrank ℝ (LinearMap.range D) := by
      rw [LinearMap.range_comp]
      exact (Submodule.finrank_map_le _ _).trans
        (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _))

/-- Derivative of the invariant block under uniform scaling of its two cores. -/
def blockScaling {R : Type*} [CommRing R] (x : Coordinate → R) (u v : R) :
    Coordinate → R :=
  fun i => (if i.1 = 0 then u else v) * (if i.2.val < 2 then 1 else 2) * x i

private theorem invariants_smul {R : Type*} [CommRing R] (A : Fin 2 → Core R)
    (c : R) (j : Fin 5) :
    invariants (fun i => c • A i) j =
      c ^ (if j.val < 2 then 1 else 2) * invariants A j := by
  fin_cases j <;> simp [invariants, Matrix.trace_smul, smul_smul, pow_two]

theorem gramDifferential_blockScaling {R : Type*} [CommRing R] (m : ℕ)
    (K B : Fin 2 → Core R) (u v : R) :
    gramDifferential m (coordinates K B) (blockScaling (coordinates K B) u v) =
      ((2 + m : ℕ) : R) • ((u + v) • gramChart m (coordinates K B)) := by
  let c := dual 1 u
  let f := dual 1 v
  let liftCore (A : Fin 2 → Core R) (i : Fin 2) := (A i).map (inlHom R R)
  have heq : (fun i => dual (coordinates K B i) (blockScaling (coordinates K B) u v i)) = coordinates (fun i => c • liftCore K i) (fun i => f • liftCore B i) := by
    have hK := map_invariants (inlHom R R) K
    have hB := map_invariants (inlHom R R) B
    funext i
    by_cases h : i.1 = 0 <;>
      simp only [coordinates, h, ite_true, ite_false, blockScaling, invariants_smul, liftCore,
        ← hK, ← hB, Function.comp_apply]
    all_goals
      split <;> apply TrivSqZeroExt.ext <;>
        simp [c, f, mul_comm]
  funext ab
  rw [gramDifferential_apply, heq]
  rw [← literalGram_eq_chart, literalGram_blockScale]
  change ((c * f) ^ (2 + m) *
    literalGram (fun i => (K i).map (inlHom R R)) (fun i => (B i).map (inlHom R R)) m ab).snd = _
  rw [← map_literalGram, literalGram_eq_chart]
  simp [c, f, nsmul_eq_mul, mul_assoc]
  ring

/-- The relative block scaling is in the kernel. At physical points this is
the complexification of the common phase direction. -/
theorem witness_phase_mem_ker (m : ℕ) :
    blockScaling witnessCoordinates 1 (-1) ∈ LinearMap.ker (gramDifferential m witnessCoordinates) := by
  rw [LinearMap.mem_ker]
  simpa [witnessCoordinates] using gramDifferential_blockScaling m
    (balancedWitnessCore ∘ ketIndex) (balancedWitnessCore ∘ braIndex) (1 : ℝ) (-1)

/-- The unnormalized invariant Jacobian has rank exactly nine at the common point. -/
theorem gramDifferential_rank_eq_nine {m : ℕ} (hm : 5 ≤ m) :
    Module.finrank ℝ (LinearMap.range (gramDifferential m witnessCoordinates)) = 9 := by
  have hphase : blockScaling witnessCoordinates 1 (-1) ≠ 0 := by
    intro h
    have heq := congrFun h ((0, 0) : Coordinate)
    norm_num [blockScaling, witnessCoordinates_eq] at heq
  have hk : 1 ≤ Module.finrank ℝ (LinearMap.ker (gramDifferential m witnessCoordinates)) :=
    Submodule.one_le_finrank_iff.mpr fun h =>
      hphase (by simpa only [h, Submodule.mem_bot] using witness_phase_mem_ker m)
  have hr := (gramDifferential m witnessCoordinates).finrank_range_add_finrank_ker
  norm_num [Module.finrank_pi, Fintype.card_prod] at hr
  have hl := nine_le_gramDifferential_rank hm
  omega

/-- Uniform scaling supplies the raw Gram value inside the differential range. -/
theorem witnessGram_mem_range (m : ℕ) :
    gramChart m witnessCoordinates ∈ LinearMap.range (gramDifferential m witnessCoordinates) := by
  have hn : ((2 + m : ℕ) : ℝ) ≠ 0 := by positivity
  refine ⟨((2 + m : ℕ) : ℝ)⁻¹ • blockScaling witnessCoordinates 1 0, ?_⟩
  rw [map_smul]
  have h := gramDifferential_blockScaling m (balancedWitnessCore ∘ ketIndex)
    (balancedWitnessCore ∘ braIndex) (1 : ℝ) 0
  change gramDifferential m witnessCoordinates (blockScaling witnessCoordinates 1 0) =
    ((2 + m : ℕ) : ℝ) • (((1 : ℝ) + 0) • gramChart m witnessCoordinates) at h
  simp only [add_zero, one_smul] at h
  rw [h, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- Quotient the Gram differential by the radial line of its exact raw value. -/
def projectiveGramDifferential (m : ℕ) : (Coordinate → ℝ) →ₗ[ℝ]
    ((Entry → ℝ) ⧸ Submodule.span ℝ {gramChart m witnessCoordinates}) :=
  (Submodule.span ℝ {gramChart m witnessCoordinates}).mkQ.comp
    (gramDifferential m witnessCoordinates)

/-- Normalization of the invariant Gram differential removes precisely the radial
direction whenever the raw Gram value is nonzero. -/
theorem projectiveGramDifferential_rank_eq_eight {m : ℕ} (hm : 5 ≤ m)
    (hvalue : gramChart m witnessCoordinates ≠ 0) :
    Module.finrank ℝ (LinearMap.range (projectiveGramDifferential m)) = 8 := by
  let D := gramDifferential m witnessCoordinates
  let V := LinearMap.range D
  let L := Submodule.span ℝ {gramChart m witnessCoordinates}
  let q := L.mkQ.comp V.subtype
  have hLV : L ≤ V := (Submodule.span_singleton_le_iff_mem _ _).mpr (witnessGram_mem_range m)
  have hk : LinearMap.ker q = L.comap V.subtype := by
    change LinearMap.ker (L.mkQ.comp V.subtype) = _
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hkdim : Module.finrank ℝ (LinearMap.ker q) = 1 := by
    rw [hk, (Submodule.comapSubtypeEquivOfLe hLV).finrank_eq]
    exact finrank_span_singleton hvalue
  have hr : LinearMap.range q = LinearMap.range (projectiveGramDifferential m) := by
    change LinearMap.range (L.mkQ.comp V.subtype) = LinearMap.range (L.mkQ.comp D)
    simp only [LinearMap.range_comp, Submodule.range_subtype, V]
  have h := q.finrank_range_add_finrank_ker
  change Module.finrank ℝ (LinearMap.range q) + Module.finrank ℝ (LinearMap.ker q) =
    Module.finrank ℝ (LinearMap.range (gramDifferential m witnessCoordinates)) at h
  rw [hr, hkdim, gramDifferential_rank_eq_nine hm] at h
  exact Nat.add_right_cancel (h.trans (show 9 = 8 + 1 by decide))

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformCommonSpectralRankTransport
