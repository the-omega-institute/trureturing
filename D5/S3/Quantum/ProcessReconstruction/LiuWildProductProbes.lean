/- GID: D5/S3/Quantum/ProcessReconstruction/LiuWildProductProbes
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/LiuWildProductProbes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact success for adaptive product probes of an explicit channel pair. -/

import D5.S3.Quantum.ProcessReconstruction.RankTwoHiddenProcess
import D5.S3.Estimation.LeCam
import D5.S3.Estimation.DecisionRisk.DescentDefectBounds
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Weil.ZetaLinear.RankTrace

/-!
Exact fixed-length discrimination for the explicit channel pair motivated by Liu–Wild §V.
The testing curve holds for any nonempty register. Both channels have Kraus rank two
for registers of at least two qubits.

Each call uses a fresh tensor product of single-qubit density states and a finite POVM on
that call's full output. The policy chooses both using its classical history and a finite
random seed with the same law under both hypotheses. Only classical data persist between
calls. A common finite alphabet accommodates the POVMs in the finite policy tree by padding
with zero effects.

The same channels induce identical maps on every proper output subsystem, even with a
retained reference. A full-output measurement on a GHZ input distinguishes them in one call.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.TotalVariation.Pinsker
open D5.S3.Quantum.Information.PartialTraceMutualInformation (density_posSemidef)
open D5.S3.Estimation.LeCam (le_cam_two_point_sum)
open UnitaryReconstruction.ParityFamily (Bits)
open UnitaryReconstruction.RankTwoHiddenProcess

namespace UnitaryReconstruction.LiuWildProductProbes

/-- Positivity of the qubit determinant and trace one bound its coherence. -/
theorem qubit_coherence_le (ρ : DensityState Bool) : ‖ρ.val false true‖ ≤ 1 / 2 := by
  let A := CStarMatrix.ofMatrix.symm ρ.val
  have hA := density_posSemidef ρ
  have hd := (Complex.nonneg_iff.mp (hA.submatrix finTwoEquiv).det_nonneg).1
  rw [Matrix.det_fin_two] at hd
  change 0 ≤ (A false false * A true true - A false true * A true false).re at hd
  have hstar : A true false = star (A false true) := (hA.isHermitian.apply true false).symm
  have hmul : A false true * star (A false true) =
      ((‖A false true‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.sq_norm]
  rw [hstar, hmul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    (Complex.nonneg_iff.mp (hA.diag_nonneg (i := false))).2.symm,
    (Complex.nonneg_iff.mp (hA.diag_nonneg (i := true))).2.symm] at hd
  have ht := congrArg Complex.re ρ.prop.2
  change A.trace.re = (1 : ℂ).re at ht
  rw [Matrix.trace, Fintype.sum_bool, Complex.add_re, Complex.one_re] at ht
  change (A true true).re + (A false false).re = 1 at ht
  change ‖A false true‖ ≤ 1 / 2
  have hsquare := congrArg (fun x : ℝ => x ^ 2) ht
  have hb : ‖A false true‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((A false false).re - (A true true).re)]
  exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp hb

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The tensor product of single-site mixed states in the word basis. -/
def productInput (ρ : ι → DensityState Bool) : DensityState (Bits ι) := by
  let A (i : ι) := CStarMatrix.ofMatrix.symm (ρ i).val
  let S (i : ι) := CFC.sqrt (A i)
  let X : Matrix (Bits ι) (Bits ι) ℂ := Matrix.of fun x y => ∏ i, A i (x i) (y i)
  let Y : Matrix (Bits ι) (Bits ι) ℂ := Matrix.of fun x y => ∏ i, S i (x i) (y i)
  have hS (i : ι) : (S i)ᴴ * S i = A i := by
    have hpos : 0 ≤ S i := CFC.sqrt_nonneg _
    rw [hpos.posSemidef.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self _ (density_posSemidef (ρ i)).nonneg]
  have hgram : Yᴴ * Y = X := by
    ext x y
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Y, X, Matrix.of_apply,
      star_prod, ← Finset.prod_mul_distrib]
    calc
      _ = ∏ i, ∑ b : Bool, star (S i b (x i)) * S i b (y i) :=
        (Fintype.prod_sum (κ := fun _ : ι => Bool)
          (fun i b => star (S i b (x i)) * S i b (y i))).symm
      _ = _ := Finset.prod_congr rfl fun i _ =>
        congrArg (fun T : Matrix Bool Bool ℂ => T (x i) (y i)) (hS i)
  refine ⟨CStarMatrix.ofMatrix X, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv ?_, ?_⟩
  · exact Matrix.nonneg_iff_posSemidef.mpr (hgram ▸ Matrix.posSemidef_conjTranspose_mul_self Y)
  · change X.trace = 1
    unfold Matrix.trace
    simp only [X, Matrix.diag_apply, Matrix.of_apply]
    calc
      _ = ∏ i, ∑ b : Bool, A i b b :=
        (Fintype.prod_sum (κ := fun _ : ι => Bool) (fun i b => A i b b)).symm
      _ = 1 := Finset.prod_eq_one fun i _ => (ρ i).prop.2

theorem product_coherence (ρ : ι → DensityState Bool) :
    (productInput ρ).val (zeroWord : Bits ι) oneWord = ∏ i, (ρ i).val false true := rfl

theorem product_coherence_le (ρ : ι → DensityState Bool) :
    ‖(productInput ρ).val (zeroWord : Bits ι) oneWord‖ ≤ (1 / 2) ^ Fintype.card ι := by
  rw [product_coherence, norm_prod]
  calc
    _ ≤ ∏ _ : ι, (1 / 2 : ℝ) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => qubit_coherence_le (ρ i))
    _ = _ := by simp

/-- The density matrix of the one-qubit plus state. -/
def plusQubit : DensityState Bool := by
  let v : Bool → ℂ := fun _ => 1
  let X := (1 / 2 : ℂ) • vecMulVec v (star v)
  have hp : X.PosSemidef :=
    (Matrix.posSemidef_vecMulVec_self_star v).smul
      (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1 / 2)
  refine ⟨CStarMatrix.ofMatrix X, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hp.nonneg, ?_⟩
  change X.trace = 1
  norm_num [Matrix.trace, Matrix.diag_apply, Fintype.sum_bool, X, v, Matrix.vecMulVec_apply]

section TwoEntries

variable {a : Type*} [Fintype a] [DecidableEq a]

private def offDiagonal (u v : a) (z : ℂ) : Matrix a a ℂ :=
  Matrix.of fun x y =>
    if x = u ∧ y = v then z else if x = v ∧ y = u then star z else 0

omit [Fintype a] in
private theorem offDiagonal_apply (u v x y : a) (z : ℂ) :
    offDiagonal u v z x y =
      if x = u ∧ y = v then z else if x = v ∧ y = u then star z else 0 := rfl

omit [Fintype a] in
private theorem offDiagonal_hermitian (u v : a) (huv : u ≠ v) (z : ℂ) :
    (offDiagonal u v z).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, offDiagonal_apply]
  by_cases hx : x = u <;> by_cases hy : y = u <;>
    by_cases hx' : x = v <;> by_cases hy' : y = v <;>
    simp_all

private theorem offDiagonal_traceNorm (u v : a) (huv : u ≠ v) (z : ℂ) :
    traceNorm (offDiagonal u v z) = 2 * ‖z‖ := by
  let d : a → ℂ := fun x => if x = u ∨ x = v then (‖z‖ : ℂ) else 0
  have hd : (diagonal d).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro x
    by_cases hx : x = u ∨ x = v <;> simp [d, hx, Complex.nonneg_iff]
  have hg : diagonal d * diagonal d = (offDiagonal u v z)ᴴ * offDiagonal u v z := by
    rw [(offDiagonal_hermitian u v huv z).eq, Matrix.diagonal_mul_diagonal]
    have hnorm : z * star z = ((‖z‖ : ℝ) : ℂ) * ((‖z‖ : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, ← Complex.sq_norm, pow_two, Complex.ofReal_mul]
    ext x y
    rw [Matrix.mul_apply]
    by_cases hx : x = u
    · subst x
      have hrow (k : a) : offDiagonal u v z u k = if k = v then z else 0 := by
        simp [offDiagonal_apply, huv]
      simp_rw [hrow, ite_mul, zero_mul]
      rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ v)]
      by_cases hy : y = u
      · subst y
        rw [show offDiagonal u v z v u = star z by simp [offDiagonal_apply, huv.symm],
          hnorm]
        simp [d]
      · rw [Matrix.diagonal_apply_ne _ (Ne.symm hy)]
        simp [offDiagonal_apply, huv.symm, hy]
    · by_cases hx' : x = v
      · subst x
        have hrow (k : a) : offDiagonal u v z v k = if k = u then star z else 0 := by
          simp [offDiagonal_apply, huv.symm]
        simp_rw [hrow, ite_mul, zero_mul]
        rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ u)]
        by_cases hy : y = v
        · subst y
          rw [show offDiagonal u v z u v = z by simp [offDiagonal_apply],
            mul_comm (star z) z, hnorm]
          simp [d]
        · rw [Matrix.diagonal_apply_ne _ (Ne.symm hy)]
          simp [offDiagonal_apply, huv, hy]
      · by_cases hxy : x = y
        · subst y
          simp [offDiagonal_apply, hx, hx', d]
        · simp [offDiagonal_apply, hx, hx', Matrix.diagonal_apply_ne _ hxy]
  have hroot := CFC.sqrt_unique hg hd.nonneg
  have hsum : (∑ x, d x) = (‖z‖ : ℂ) + (‖z‖ : ℂ) := by
    have he : d = fun x => (if x = u then (‖z‖ : ℂ) else 0) +
        (if x = v then (‖z‖ : ℂ) else 0) := by
      funext x
      by_cases hx : x = u <;> by_cases hy : x = v <;> simp_all [d]
    simp [he, Finset.sum_add_distrib]
  change (CFC.sqrt ((offDiagonal u v z)ᴴ * offDiagonal u v z)).trace.re = _
  rw [hroot, Matrix.trace_diagonal, hsum, Complex.add_re, Complex.ofReal_re, two_mul]

private theorem hiddenChannel_sub (u v : a) (huv : u ≠ v)
    (X : Matrix a a ℂ) (hX : X.IsHermitian) :
    act (hiddenChannel u v false) X - act (hiddenChannel u v true) X =
      offDiagonal u v (2 * X u v) := by
  ext x y
  change (hiddenChannel u v false).toCompletelyPositiveMap (CStarMatrix.ofMatrix X) x y -
    (hiddenChannel u v true).toCompletelyPositiveMap (CStarMatrix.ofMatrix X) x y = _
  rw [offDiagonal_apply]
  by_cases hxy : x = u ∧ y = v
  · obtain ⟨rfl, rfl⟩ := hxy
    rw [hiddenChannel_entry, hiddenChannel_entry]
    simp [inBlock, phase, huv]
    ring
  · by_cases hyx : x = v ∧ y = u
    · obtain ⟨hx, hy⟩ := hyx
      subst x
      subst y
      rw [hiddenChannel_entry, hiddenChannel_entry]
      have hstar : X v u = star (X u v) := (hX.apply v u).symm
      rw [hstar]
      simp [inBlock, phase, huv, huv.symm]
      ring
    · simp [hxy, hyx, hiddenChannel_entry_eq u v X x y hxy hyx]

end TwoEntries

section NonemptyRegister

variable [Nonempty ι]

omit [Fintype ι] [DecidableEq ι] in
private theorem words_ne : (zeroWord : Bits ι) ≠ oneWord := by
  intro h
  have hbit := congrFun h (Classical.choice (inferInstance : Nonempty ι))
  cases hbit

/-- The pair reads exactly the extreme-word coherence, with unhalved trace norm. -/
theorem output_traceNorm_eq (ρ : DensityState (Bits ι)) :
    traceNorm (act (channel false) (CStarMatrix.ofMatrix.symm ρ.val) -
      act (channel true) (CStarMatrix.ofMatrix.symm ρ.val)) =
      4 * ‖ρ.val (zeroWord : Bits ι) oneWord‖ := by
  unfold channel
  rw [hiddenChannel_sub _ _ words_ne _ (density_posSemidef ρ).isHermitian,
    offDiagonal_traceNorm _ _ words_ne, norm_mul]
  norm_num
  ring

theorem product_output_traceNorm_le (ρ : ι → DensityState Bool) :
    traceNorm (act (channel false) (CStarMatrix.ofMatrix.symm (productInput ρ).val) -
      act (channel true) (CStarMatrix.ofMatrix.symm (productInput ρ).val)) ≤
      4 / (2 : ℝ) ^ Fintype.card ι := by
  rw [output_traceNorm_eq, div_eq_mul_inv, ← inv_pow]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [one_div] using product_coherence_le ρ) (by norm_num)

theorem all_plus_output_traceNorm (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    let ρ := productInput (fun _ : ι => plusQubit)
    traceNorm (act (channel false) (CStarMatrix.ofMatrix.symm ρ.val) -
      act (channel true) (CStarMatrix.ofMatrix.symm ρ.val)) = 4 / (2 : ℝ) ^ Fintype.card ι := by
  dsimp only
  rw [output_traceNorm_eq, product_coherence, norm_prod]
  have hp : ‖plusQubit.val false true‖ = 1 / 2 := by
    change ‖(1 / 2 : ℂ) * (1 * star 1)‖ = 1 / 2
    norm_num [norm_div]
  rw [show (4 / (2 : ℝ) ^ Fintype.card ι) = 4 * (1 / 2) ^ Fintype.card ι by
    rw [one_div, inv_pow, div_eq_mul_inv]]
  simp [hp]

section Measurement

variable {a Ω : Type*} [Fintype a] [DecidableEq a] [Fintype Ω]

/-- A finite POVM on the full output space, with no locality restriction on its effects. -/
structure FinitePOVM (a Ω : Type*) [Fintype a] [DecidableEq a] [Fintype Ω] where
  effect : Ω → Matrix a a ℂ
  positive : ∀ o, (effect o).PosSemidef
  complete : ∑ o, effect o = 1

def bornMass (E : FinitePOVM a Ω) (A : Matrix a a ℂ) (o : Ω) : ℝ :=
  (E.effect o * A).trace.re

private theorem sum_bornMass (E : FinitePOVM a Ω) (A : Matrix a a ℂ) :
    ∑ o, bornMass E A o = A.trace.re := by
  unfold bornMass
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, E.complete, Matrix.one_mul]

/-- Measurement converts at most half the unhalved trace norm into total variation. -/
theorem povm_totalVariation_le (E : FinitePOVM a Ω) (A B : Matrix a a ℂ)
    (h : (A - B).IsHermitian) :
    totalVariation (bornMass E A) (bornMass E B) ≤ traceNorm (A - B) / 2 := by
  let P := posPart (A - B)
  let N := negPart (A - B)
  have hP : P.PosSemidef := (CFC.posPart_nonneg _).posSemidef
  have hN : N.PosSemidef := (CFC.negPart_nonneg _).posSemidef
  have hsplit : P - N = A - B := CFC.posPart_sub_negPart _ h
  have hpoint (o : Ω) : |bornMass E A o - bornMass E B o| ≤
      bornMass E P o + bornMass E N o := by
    have he : bornMass E A o - bornMass E B o = bornMass E P o - bornMass E N o := by
      simpa only [bornMass, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] using
        congrArg (fun X : Matrix a a ℂ => (E.effect o * X).trace.re) hsplit.symm
    rw [he]
    have hp : 0 ≤ bornMass E P o := RHLinalg.trace_mul_nonneg_of_posSemidef (E.positive o) hP
    have hn : 0 ≤ bornMass E N o := RHLinalg.trace_mul_nonneg_of_posSemidef (E.positive o) hN
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsum := Finset.sum_le_sum (fun o (_ : o ∈ Finset.univ) => hpoint o)
  rw [Finset.sum_add_distrib, sum_bornMass, sum_bornMass] at hsum
  rw [totalVariation, trace_norm_jordan_mass _ h]
  linarith

end Measurement

open D5.S3.Estimation.DecisionRisk.DescentDefectBounds (FiniteMarkovKernel)

/-- One query's product input and global measurement. -/
structure ProductProbe (ι Ω : Type*) [Fintype ι] [DecidableEq ι] [Fintype Ω] where
  localState : ι → DensityState Bool
  measurement : FinitePOVM (Bits ι) Ω

variable {Ω : Type*} [Fintype Ω]

private def outputState (flip : Bool) (ρ : ι → DensityState Bool) : DensityState (Bits ι) :=
  (channel flip).mapState (productInput ρ)

/-- Its conditional outcome law is a stochastic row for each channel hypothesis. -/
def probeKernel (flip : Bool) : FiniteMarkovKernel (ProductProbe ι Ω) Ω := by
  refine ⟨fun q => bornMass q.measurement (CStarMatrix.ofMatrix.symm
    (outputState flip q.localState).val), ⟨?_, ?_⟩⟩
  · intro q o
    exact RHLinalg.trace_mul_nonneg_of_posSemidef (q.measurement.positive o)
      (density_posSemidef (outputState flip q.localState))
  · intro q
    rw [sum_bornMass]
    exact congrArg Complex.re (outputState flip q.localState).prop.2

theorem product_probe_totalVariation_le (q : ProductProbe ι Ω) :
    totalVariation ((probeKernel false).val q) ((probeKernel true).val q) ≤
      2 / (2 : ℝ) ^ Fintype.card ι := by
  have h := povm_totalVariation_le q.measurement _ _
    ((density_posSemidef (outputState false q.localState)).isHermitian.sub
      (density_posSemidef (outputState true q.localState)).isHermitian)
  have hnorm := product_output_traceNorm_le q.localState
  change totalVariation ((probeKernel false).val q) ((probeKernel true).val q) ≤
    traceNorm (act (channel false) (CStarMatrix.ofMatrix.symm (productInput q.localState).val) -
      act (channel true) (CStarMatrix.ofMatrix.symm (productInput q.localState).val)) / 2 at h
  exact h.trans ((div_le_div_of_nonneg_right hnorm (by norm_num)).trans_eq (by ring))

namespace Adaptive

/-- A fixed-length ordered transcript. -/
def Transcript (Ω : Type*) : ℕ → Type _
  | 0 => PUnit
  | m + 1 => Ω × Transcript Ω m

instance transcriptFintype (Ω : Type*) [Fintype Ω] (m : ℕ) : Fintype (Transcript Ω m) :=
  match m with
  | 0 => inferInstanceAs (Fintype PUnit)
  | m + 1 =>
    letI := transcriptFintype Ω m
    inferInstanceAs (Fintype (Ω × Transcript Ω m))

/-- At each history, the policy chooses a query before seeing the next outcome. -/
inductive Policy (Q Ω : Type*) : ℕ → Type _
  | done : Policy Q Ω 0
  | query {m} (q : Q) (next : Ω → Policy Q Ω m) : Policy Q Ω (m + 1)

def jointLaw {A B : Type*} (p : A → ℝ) (K : A → B → ℝ) : A × B → ℝ :=
  fun x => p x.1 * K x.1 x.2

private theorem jointLaw_sum {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (K : A → B → ℝ) (hK : ∀ a, ∑ b, K a b = 1) :
    ∑ x, jointLaw p K x = ∑ a, p a := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp only [jointLaw, ← Finset.mul_sum, hK, mul_one]

def law {Q Ω : Type*} [Fintype Ω] (K : FiniteMarkovKernel Q Ω) :
    {m : ℕ} → Policy Q Ω m → Transcript Ω m → ℝ
  | 0, .done => fun _ => 1
  | _ + 1, .query q next => jointLaw (K.val q) (fun o => law K (next o))

private theorem law_nonneg {Q Ω : Type*} [Fintype Ω] (K : FiniteMarkovKernel Q Ω)
    {m : ℕ} (p : Policy Q Ω m) (x : Transcript Ω m) : 0 ≤ law K p x := by
  induction p with
  | done => exact zero_le_one
  | query q next ih => exact mul_nonneg (K.prop.1 q x.1) (ih x.1 x.2)

private theorem law_sum {Q Ω : Type*} [Fintype Ω] (K : FiniteMarkovKernel Q Ω)
    {m : ℕ} (p : Policy Q Ω m) : ∑ x, law K p x = 1 := by
  induction p with
  | done =>
    change (∑ _ : PUnit, (1 : ℝ)) = 1
    simp
  | query q next ih =>
    change ∑ x, jointLaw (K.val q) (fun o => law K (next o)) x = 1
    rw [jointLaw_sum _ _ ih, K.prop.2]

/-- Include the shared finite seed in the transcript so the final test can use it. -/
def seededLaw {Q Ω S : Type*} [Fintype Ω] (K : FiniteMarkovKernel Q Ω) {m : ℕ}
    (seed : S → ℝ) (p : S → Policy Q Ω m) : S × Transcript Ω m → ℝ :=
  jointLaw seed (fun s => law K (p s))

theorem seededLaw_sum {Q Ω S : Type*} [Fintype Ω] [Fintype S]
    (K : FiniteMarkovKernel Q Ω) {m : ℕ} (seed : S → ℝ) (p : S → Policy Q Ω m)
    (hseed : ∑ s, seed s = 1) : ∑ x, seededLaw K seed p x = 1 := by
  rw [seededLaw, jointLaw_sum _ _ (fun s => law_sum K (p s)), hseed]

/-- For normalized finite rows, the complement of total variation is their overlap. -/
theorem one_sub_totalVariation_eq_sum_min {A : Type*} [Fintype A] (p q : A → ℝ)
    (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    1 - totalVariation p q = ∑ a, min (p a) (q a) := by
  have point (a : A) : |p a - q a| = p a + q a - 2 * min (p a) (q a) := by
    rcases le_total (p a) (q a) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h), min_eq_left h]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr h), min_eq_right h]
      ring
  simp_rw [totalVariation, point]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hp, hq]
  ring

/-- The overlap of two joint laws is at least the overlap of their first marginals
times a uniform lower bound on the overlap of corresponding conditional rows. -/
theorem jointLaw_one_sub_totalVariation_ge {A B : Type*} [Fintype A] [Fintype B]
    (p q : A → ℝ) (K L : FiniteMarkovKernel A B) (δ : ℝ)
    (hp₀ : ∀ a, 0 ≤ p a) (hq₀ : ∀ a, 0 ≤ q a)
    (hp₁ : ∑ a, p a = 1) (hq₁ : ∑ a, q a = 1)
    (hrow : ∀ a, totalVariation (K.val a) (L.val a) ≤ δ) :
    (1 - totalVariation p q) * (1 - δ) ≤
      1 - totalVariation (jointLaw p K.val) (jointLaw q L.val) := by
  rw [one_sub_totalVariation_eq_sum_min p q hp₁ hq₁,
    one_sub_totalVariation_eq_sum_min _ _ ((jointLaw_sum _ _ K.prop.2).trans hp₁)
      ((jointLaw_sum _ _ L.prop.2).trans hq₁),
    Finset.sum_mul, Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro a _
  have hOverlap : 1 - δ ≤ ∑ b, min (K.val a b) (L.val a b) := by
    rw [← one_sub_totalVariation_eq_sum_min _ _ (K.prop.2 a) (L.prop.2 a)]
    exact sub_le_sub_left (hrow a) 1
  calc
    _ ≤ min (p a) (q a) * ∑ b, min (K.val a b) (L.val a b) :=
      mul_le_mul_of_nonneg_left hOverlap (le_min (hp₀ a) (hq₀ a))
    _ ≤ _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro b _
      exact le_min
        (mul_le_mul (min_le_left _ _) (min_le_left _ _)
          (le_min (K.prop.1 a b) (L.prop.1 a b)) (hp₀ a))
        (mul_le_mul (min_le_right _ _) (min_le_right _ _)
          (le_min (K.prop.1 a b) (L.prop.1 a b)) (hq₀ a))

/-- A uniform per-query TV bound gives a multiplicative lower bound on transcript overlap. -/
theorem transcript_totalVariation_sharp_le {Q Ω : Type*} [Fintype Ω]
    (K L : FiniteMarkovKernel Q Ω) (ε : ℝ) (hε : ε ≤ 1)
    (hrow : ∀ q, totalVariation (K.val q) (L.val q) ≤ ε)
    {m : ℕ} (p : Policy Q Ω m) :
    totalVariation (law K p) (law L p) ≤ 1 - (1 - ε) ^ m := by
  induction p with
  | done => simp [law, totalVariation]
  | @query m q next ih =>
    let K' : FiniteMarkovKernel Ω (Transcript Ω m) :=
      ⟨fun o => law K (next o), ⟨fun o => law_nonneg K (next o), fun o => law_sum K (next o)⟩⟩
    let L' : FiniteMarkovKernel Ω (Transcript Ω m) :=
      ⟨fun o => law L (next o), ⟨fun o => law_nonneg L (next o), fun o => law_sum L (next o)⟩⟩
    have h := jointLaw_one_sub_totalVariation_ge (K.val q) (L.val q) K' L'
      (1 - (1 - ε) ^ m) (K.prop.1 q) (L.prop.1 q) (K.prop.2 q) (L.prop.2 q) ih
    change _ ≤ 1 - totalVariation (law K (.query q next)) (law L (.query q next)) at h
    rw [sub_sub_cancel] at h
    have hmul := mul_le_mul_of_nonneg_right (sub_le_sub_left (hrow q) 1)
      (pow_nonneg (sub_nonneg.mpr hε) m)
    rw [pow_succ']
    linarith only [hmul.trans h]

/-- A shared finite seed can be included in the transcript at the same sharp TV bound. -/
theorem seeded_transcript_totalVariation_sharp_le {Q Ω S : Type*} [Fintype Ω] [Fintype S]
    (K L : FiniteMarkovKernel Q Ω) (ε : ℝ) (hε : ε ≤ 1)
    (hrow : ∀ q, totalVariation (K.val q) (L.val q) ≤ ε)
    {m : ℕ} (seed : S → ℝ) (p : S → Policy Q Ω m)
    (hs₀ : ∀ s, 0 ≤ seed s) (hs₁ : ∑ s, seed s = 1) :
    totalVariation (seededLaw K seed p) (seededLaw L seed p) ≤ 1 - (1 - ε) ^ m := by
  let K' : FiniteMarkovKernel S (Transcript Ω m) :=
    ⟨fun s => law K (p s), ⟨fun s => law_nonneg K (p s), fun s => law_sum K (p s)⟩⟩
  let L' : FiniteMarkovKernel S (Transcript Ω m) :=
    ⟨fun s => law L (p s), ⟨fun s => law_nonneg L (p s), fun s => law_sum L (p s)⟩⟩
  have h := jointLaw_one_sub_totalVariation_ge seed seed K' L' (1 - (1 - ε) ^ m) hs₀ hs₀ hs₁ hs₁
    (fun s => transcript_totalVariation_sharp_le K L ε hε hrow (p s))
  change _ ≤ 1 - totalVariation (seededLaw K seed p) (seededLaw L seed p) at h
  have hs : totalVariation seed seed = 0 := by simp [totalVariation]
  rw [hs, sub_zero, one_mul, sub_sub_cancel] at h
  linarith only [h]

end Adaptive

open Adaptive

/-- The probability of the correct conclusive outcome of the all-plus probe. -/
def conclusiveMass (ι : Type*) [Fintype ι] : ℝ := 2 / (2 : ℝ) ^ Fintype.card ι

omit [DecidableEq ι] in
theorem conclusiveMass_le_one : conclusiveMass ι ≤ 1 := by
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hpow : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ Fintype.card ι := pow_le_pow_right₀ (by norm_num) hcard
  exact (div_le_one (by positivity)).mpr (by simpa using hpow)

theorem product_transcript_totalVariation_sharp_le {S : Type*} [Fintype S] {M : ℕ}
    (seed : S → ℝ) (policy : S → Policy (ProductProbe ι Ω) Ω M)
    (hs₀ : ∀ s, 0 ≤ seed s) (hs₁ : ∑ s, seed s = 1) :
    totalVariation (seededLaw (probeKernel false) seed policy)
      (seededLaw (probeKernel true) seed policy) ≤ 1 - (1 - conclusiveMass ι) ^ M :=
  seeded_transcript_totalVariation_sharp_le _ _ _ conclusiveMass_le_one
    product_probe_totalVariation_le seed policy hs₀ hs₁

omit [DecidableEq ι] in
private theorem conclusiveMass_bernoulli (M : ℕ) :
    1 - (M : ℝ) * conclusiveMass ι ≤ (1 - conclusiveMass ι) ^ M := by
  have h : (-2 : ℝ) ≤ -conclusiveMass ι := by linarith only [conclusiveMass_le_one (ι := ι)]
  simpa only [mul_neg, ← sub_eq_add_neg] using one_add_mul_le_pow h M

/-- The linear transcript bound follows from the sharp overlap bound by Bernoulli. -/
theorem product_transcript_totalVariation_le {S : Type*} [Fintype S] {M : ℕ}
    (seed : S → ℝ) (policy : S → Policy (ProductProbe ι Ω) Ω M)
    (hs₀ : ∀ s, 0 ≤ seed s) (hs₁ : ∑ s, seed s = 1) :
    totalVariation (seededLaw (probeKernel false) seed policy)
      (seededLaw (probeKernel true) seed policy) ≤
        (M : ℝ) * (2 / (2 : ℝ) ^ Fintype.card ι) := by
  change _ ≤ (M : ℝ) * conclusiveMass ι
  linarith only [product_transcript_totalVariation_sharp_le seed policy hs₀ hs₁,
    conclusiveMass_bernoulli (ι := ι) M]

open Classical in
/-- The exact equal-prior success upper bound, with the decision to guess `true` on `accept`. -/
theorem liu_wild_product_input_success_le
    {S : Type*} [Fintype S] {M : ℕ}
    (seed : S → ℝ) (policy : S → Policy (ProductProbe ι Ω) Ω M)
    (hs₀ : ∀ s, 0 ≤ seed s) (hs₁ : ∑ s, seed s = 1)
    (accept : Finset (S × Transcript Ω M)) :
    ((∑ t ∈ acceptᶜ, seededLaw (probeKernel false) seed policy t) +
      (∑ t ∈ accept, seededLaw (probeKernel true) seed policy t)) / 2 ≤
      1 - (1 - conclusiveMass ι) ^ M / 2 := by
  let p := seededLaw (probeKernel false) seed policy
  let q := seededLaw (probeKernel true) seed policy
  have hp : ∑ t, p t = 1 := seededLaw_sum _ _ _ hs₁
  have hq : ∑ t, q t = 1 := seededLaw_sum _ _ _ hs₁
  have herror : 1 - totalVariation p q ≤ (∑ t ∈ accept, p t) + (∑ t ∈ acceptᶜ, q t) := by
    convert le_cam_two_point_sum p q accept (hp.trans hq.symm) hq using 3
    exact Finset.ext fun _ => by simp only [Finset.mem_compl]
  have hpSplit : (∑ t ∈ accept, p t) + (∑ t ∈ acceptᶜ, p t) = 1 :=
    (Finset.sum_add_sum_compl accept p).trans hp
  have hqSplit : (∑ t ∈ accept, q t) + (∑ t ∈ acceptᶜ, q t) = 1 :=
    (Finset.sum_add_sum_compl accept q).trans hq
  have htv : totalVariation p q ≤ 1 - (1 - conclusiveMass ι) ^ M :=
    product_transcript_totalVariation_sharp_le seed policy hs₀ hs₁
  change ((∑ t ∈ acceptᶜ, p t) + (∑ t ∈ accept, q t)) / 2 ≤ _
  linarith only [herror, hpSplit, hqSplit, htv]

open Classical in
/-- The same upper bound applies to the smaller of the two branch success probabilities. -/
theorem liu_wild_product_input_worst_case_success_le
    {S : Type*} [Fintype S] {M : ℕ}
    (seed : S → ℝ) (policy : S → Policy (ProductProbe ι Ω) Ω M)
    (hs₀ : ∀ s, 0 ≤ seed s) (hs₁ : ∑ s, seed s = 1)
    (accept : Finset (S × Transcript Ω M)) :
    min (∑ t ∈ acceptᶜ, seededLaw (probeKernel false) seed policy t)
      (∑ t ∈ accept, seededLaw (probeKernel true) seed policy t) ≤
      1 - (1 - conclusiveMass ι) ^ M / 2 := by
  have h := liu_wild_product_input_success_le seed policy hs₀ hs₁ accept
  let x := ∑ t ∈ acceptᶜ, seededLaw (probeKernel false) seed policy t
  let y := ∑ t ∈ accept, seededLaw (probeKernel true) seed policy t
  change min x y ≤ _
  change (x + y) / 2 ≤ _ at h
  linarith only [min_le_left x y, min_le_right x y, h]

open Classical in
/-- The necessary failure-factor threshold for equal-prior success at least two thirds. -/
theorem liu_wild_product_input_sharp_call_lower_bound
    {S : Type*} [Fintype S] {M : ℕ}
    (seed : S → ℝ) (policy : S → Policy (ProductProbe ι Ω) Ω M)
    (hs₀ : ∀ s, 0 ≤ seed s) (hs₁ : ∑ s, seed s = 1)
    (accept : Finset (S × Transcript Ω M))
    (success : (2 / 3 : ℝ) ≤
      ((∑ t ∈ acceptᶜ, seededLaw (probeKernel false) seed policy t) +
       (∑ t ∈ accept, seededLaw (probeKernel true) seed policy t)) / 2) :
    (1 - conclusiveMass ι) ^ M ≤ 2 / 3 := by
  linarith only [success, liu_wild_product_input_success_le seed policy hs₀ hs₁ accept]

open Classical in
/-- The exponential call lower bound for equal-prior success at least two thirds. -/
theorem liu_wild_product_input_call_lower_bound
    {S : Type*} [Fintype S] {M : ℕ}
    (seed : S → ℝ) (policy : S → Policy (ProductProbe ι Ω) Ω M)
    (hs₀ : ∀ s, 0 ≤ seed s) (hs₁ : ∑ s, seed s = 1)
    (accept : Finset (S × Transcript Ω M))
    (success : (2 / 3 : ℝ) ≤
      ((∑ t ∈ acceptᶜ, seededLaw (probeKernel false) seed policy t) +
       (∑ t ∈ accept, seededLaw (probeKernel true) seed policy t)) / 2) :
    (2 : ℝ) ^ Fintype.card ι / 6 ≤ (M : ℝ) := by
  have hfailure := liu_wild_product_input_sharp_call_lower_bound seed policy hs₀ hs₁ accept success
  have h : (1 / 3 : ℝ) ≤ (M : ℝ) * conclusiveMass ι := by
    linarith only [hfailure, conclusiveMass_bernoulli (ι := ι) M]
  unfold conclusiveMass at h
  have hd : 0 < (2 : ℝ) ^ Fintype.card ι := by positivity
  rw [← mul_div_assoc] at h
  have h' := (le_div_iff₀ hd).mp h
  linarith

open Classical in
/-- The call lower bound for success at least two thirds on both channels. -/
theorem liu_wild_product_input_worst_case_call_lower_bound
    {S : Type*} [Fintype S] {M : ℕ}
    (seed : S → ℝ) (policy : S → Policy (ProductProbe ι Ω) Ω M)
    (hs₀ : ∀ s, 0 ≤ seed s) (hs₁ : ∑ s, seed s = 1)
    (accept : Finset (S × Transcript Ω M))
    (successFalse : (2 / 3 : ℝ) ≤ ∑ t ∈ acceptᶜ, seededLaw (probeKernel false) seed policy t)
    (successTrue : (2 / 3 : ℝ) ≤ ∑ t ∈ accept, seededLaw (probeKernel true) seed policy t) :
    (2 : ℝ) ^ Fintype.card ι / 6 ≤ (M : ℝ) :=
  liu_wild_product_input_call_lower_bound seed policy hs₀ hs₁ accept (by linarith)

private def ghzSign (b : Bool) : ℂ := if b then -1 else 1

private def ghzDirection (ι : Type*) [Fintype ι] [DecidableEq ι] (b : Bool) : Bits ι → ℂ :=
  Pi.single zeroWord 1 + Pi.single oneWord (ghzSign b)

/-- The projector onto the GHZ direction with relative phase `(+1)` or `(-1)`. -/
def ghzProjector (ι : Type*) [Fintype ι] [DecidableEq ι] (b : Bool) : Matrix (Bits ι) (Bits ι) ℂ :=
  (1 / 2 : ℂ) • vecMulVec (ghzDirection ι b) (star (ghzDirection ι b))

omit [Nonempty ι] in
private theorem ghzDirection_star (b : Bool) : star (ghzDirection ι b) = ghzDirection ι b := by
  funext x
  change star (ghzDirection ι b x) = ghzDirection ι b x
  simp only [ghzDirection, Pi.add_apply, star_add, Pi.single_apply]
  split_ifs <;> cases b <;> norm_num [ghzSign]

omit [Nonempty ι] in
private theorem ghzProjector_positive (b : Bool) : (ghzProjector ι b).PosSemidef :=
  (Matrix.posSemidef_vecMulVec_self_star _).smul
    (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1 / 2)

/-- Each conclusive effect is a rank-one orthogonal projector. -/
theorem ghzProjector_rank_one (b : Bool) :
    (ghzProjector ι b).IsHermitian ∧
    ghzProjector ι b * ghzProjector ι b = ghzProjector ι b ∧
    (ghzProjector ι b).rank = 1 := by
  let v := ghzDirection ι b
  let P := ghzProjector ι b
  have huv : (zeroWord : Bits ι) ≠ oneWord := words_ne
  have hv : v zeroWord = 1 := by simp [v, ghzDirection, huv]
  have hnorm : star v ⬝ᵥ v = 2 := by
    change star (ghzDirection ι b) ⬝ᵥ ghzDirection ι b = 2
    rw [ghzDirection_star]
    conv_lhs =>
      rhs
      unfold ghzDirection
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    cases b <;> norm_num [ghzDirection, Pi.single_apply, huv, huv.symm, ghzSign]
  have hAction (x : Bits ι → ℂ) : P *ᵥ x = ((1 / 2 : ℂ) * (star v ⬝ᵥ x)) • v := by
    change ((1 / 2 : ℂ) • vecMulVec v (star v)) *ᵥ x = _
    rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, smul_smul]
  have hfix : P *ᵥ v = v := by
    rw [hAction, hnorm]
    norm_num
  refine ⟨(ghzProjector_positive b).isHermitian, ?_, ?_⟩
  · change P * P = P
    apply Matrix.ext_iff_mulVec.mpr
    intro x
    rw [← Matrix.mulVec_mulVec, hAction x, Matrix.mulVec_smul, hfix]
  · change P.rank = 1
    have hRange : LinearMap.range P.mulVecLin = Submodule.span ℂ {v} := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        rw [Matrix.mulVecLin_apply, hAction]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
      · exact (Submodule.span_singleton_le_iff_mem v _).mpr ⟨v, hfix⟩
    rw [Matrix.rank, hRange]
    exact finrank_span_singleton (by
      intro h
      simp [h] at hv)

omit [Nonempty ι] in
private theorem ghzProjector_trace_mul (b : Bool) (A : Matrix (Bits ι) (Bits ι) ℂ) :
    (ghzProjector ι b * A).trace =
      (1 / 2 : ℂ) * (A zeroWord zeroWord + A oneWord oneWord +
        ghzSign b * A zeroWord oneWord + ghzSign b * A oneWord zeroWord) := by
  rw [ghzProjector, Matrix.smul_mul, Matrix.trace_smul, ghzDirection_star,
    Matrix.vecMulVec_mul, Matrix.trace_vecMulVec]
  unfold ghzDirection
  rw [Matrix.add_vecMul]
  simp only [add_dotProduct, dotProduct_add, single_dotProduct, Matrix.single_vecMul,
    Pi.smul_apply, smul_eq_mul, Matrix.row_apply]
  cases b <;> simp [ghzSign] <;> ring

private theorem ghzProjector_add :
    ghzProjector ι false + ghzProjector ι true =
      diagonal (fun x : Bits ι => if x = zeroWord ∨ x = oneWord then (1 : ℂ) else 0) := by
  have huv : (zeroWord : Bits ι) ≠ oneWord := words_ne
  ext x y
  simp only [Matrix.add_apply, ghzProjector, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, ghzDirection, Pi.add_apply, Pi.single_apply]
  by_cases hx : x = zeroWord <;> by_cases hy : y = zeroWord <;>
    by_cases hx' : x = oneWord <;> by_cases hy' : y = oneWord <;>
    simp_all [Matrix.diagonal_apply, ghzSign, eq_comm] <;> norm_num

/-- The fixed global POVM. The two GHZ projectors give conclusive outcomes and
the complementary effect gives `none`. -/
def ghzPOVM (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    FinitePOVM (Bits ι) (Option Bool) where
  effect
    | some b => ghzProjector ι b
    | none => 1 - (ghzProjector ι false + ghzProjector ι true)
  positive := by
    intro o
    cases o with
    | some b => exact ghzProjector_positive b
    | none =>
      change (1 - (ghzProjector ι false + ghzProjector ι true)).PosSemidef
      rw [ghzProjector_add, ← Matrix.diagonal_one, Matrix.diagonal_sub,
        Matrix.posSemidef_diagonal_iff]
      intro x
      by_cases h : x = zeroWord ∨ x = oneWord <;> simp [h]
  complete := by
    rw [Fintype.sum_option, Fintype.sum_bool]
    change (1 - (ghzProjector ι false + ghzProjector ι true)) +
      (ghzProjector ι true + ghzProjector ι false) = 1
    abel

/-- The same independent all-plus input and global GHZ measurement are used on every call. -/
def allPlusGHZProbe (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    ProductProbe ι (Option Bool) :=
  ⟨fun _ => plusQubit, ghzPOVM ι⟩

omit [Nonempty ι] in
private theorem allPlus_entry (x y : Bits ι) :
    (productInput (fun _ : ι => plusQubit)).val x y = (1 / 2 : ℂ) ^ Fintype.card ι := by
  change (∏ i : ι, (1 / 2 : ℂ) * (1 * star 1)) = _
  simp

omit [Nonempty ι] in
private theorem allPlus_output_entry (flip : Bool) (x y : Bits ι)
    (hx : x = zeroWord ∨ x = oneWord) (hy : y = zeroWord ∨ y = oneWord) :
    (outputState flip (fun _ : ι => plusQubit)).val x y =
      phase oneWord flip x * ((1 / 2 : ℂ) ^ Fintype.card ι) * phase oneWord flip y := by
  change (hiddenChannel zeroWord oneWord flip).toCompletelyPositiveMap
    (CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm
      (productInput (fun _ : ι => plusQubit)).val)) x y = _
  rw [hiddenChannel_entry]
  simp [inBlock, hx, hy, allPlus_entry]

/-- An independent all-plus probe gives the correct conclusive outcome with mass
`2 / 2^n` and the wrong conclusive outcome with mass zero. -/
theorem allPlusGHZProbe_conclusive (flip b : Bool) :
    (probeKernel flip).val (allPlusGHZProbe ι) (some b) =
      if b = flip then conclusiveMass ι else 0 := by
  let A := CStarMatrix.ofMatrix.symm (outputState flip (fun _ : ι => plusQubit)).val
  change (ghzProjector ι b * A).trace.re = _
  rw [ghzProjector_trace_mul]
  have h (x y : Bits ι) (hx : x = zeroWord ∨ x = oneWord) (hy : y = zeroWord ∨ y = oneWord) :
      A x y = phase oneWord flip x * ((1 / 2 : ℂ) ^ Fintype.card ι) * phase oneWord flip y :=
    allPlus_output_entry flip x y hx hy
  rw [h _ _ (Or.inl rfl) (Or.inl rfl), h _ _ (Or.inr rfl) (Or.inr rfl),
    h _ _ (Or.inl rfl) (Or.inr rfl), h _ _ (Or.inr rfl) (Or.inl rfl)]
  have huv : (zeroWord : Bits ι) ≠ oneWord := words_ne
  let c := (1 / 2 : ℝ) ^ Fintype.card ι
  have hc : (1 / 2 : ℂ) ^ Fintype.card ι = (c : ℂ) := by
    simp [c, Complex.ofReal_pow]
  have hp : conclusiveMass ι = 2 * c := by
    simp [conclusiveMass, c, div_eq_mul_inv, inv_pow]
  rw [hc, hp]
  cases b <;> cases flip <;>
    norm_num [phase, ghzSign, huv, Complex.mul_re, Complex.mul_im, Complex.add_re] <;> ring

theorem allPlusGHZProbe_inconclusive (flip : Bool) :
    (probeKernel flip).val (allPlusGHZProbe ι) none = 1 - conclusiveMass ι := by
  have h := (probeKernel flip).prop.2 (allPlusGHZProbe ι)
  rw [Fintype.sum_option, Fintype.sum_bool, allPlusGHZProbe_conclusive,
    allPlusGHZProbe_conclusive] at h
  cases flip <;> simp at h <;> linarith

/-- Repeat the all-plus GHZ probe for exactly the prescribed number of calls. -/
def allPlusGHZPolicy (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    (m : ℕ) → Policy (ProductProbe ι (Option Bool)) (Option Bool) m
  | 0 => .done
  | m + 1 => .query (allPlusGHZProbe ι) (fun _ => allPlusGHZPolicy ι m)

/-- Guess the first conclusive label, using the seed when the whole transcript is inconclusive. -/
def ghzGuess (seed : Bool) : {m : ℕ} → Transcript (Option Bool) m → Bool
  | 0, _ => seed
  | _ + 1, (o, t) => o.getD (ghzGuess seed t)

private theorem allPlusGHZPolicy_success (flip seed : Bool) (m : ℕ) :
    (∑ t, if ghzGuess seed t = flip
      then law (probeKernel flip) (allPlusGHZPolicy ι m) t else 0) =
      1 - (1 - conclusiveMass ι) ^ m * (if seed = flip then 0 else 1) := by
  induction m with
  | zero =>
    change (∑ _ : PUnit, if seed = flip then (1 : ℝ) else 0) = _
    by_cases h : seed = flip <;> simp [h]
  | succ m ih =>
    let K := probeKernel (ι := ι) (Ω := Option Bool) flip
    let q := allPlusGHZProbe ι
    let P := law K (allPlusGHZPolicy ι m)
    change (∑ x : Option Bool × Transcript (Option Bool) m,
      if x.1.getD (ghzGuess seed x.2) = flip then K.val q x.1 * P x.2 else 0) = _
    rw [Fintype.sum_prod_type]
    have hFactor (o : Option Bool) :
        (∑ t, if o.getD (ghzGuess seed t) = flip then K.val q o * P t else 0) =
          K.val q o * ∑ t, if o.getD (ghzGuess seed t) = flip then P t else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      split <;> simp_all
    have hsum : ∑ t, P t = 1 := law_sum K (allPlusGHZPolicy ι m)
    change (∑ t, if ghzGuess seed t = flip then P t else 0) = _ at ih
    simp_rw [hFactor]
    dsimp only [K, q]
    rw [Fintype.sum_option, Fintype.sum_bool]
    simp only [Option.getD_none, Option.getD_some, allPlusGHZProbe_inconclusive,
      allPlusGHZProbe_conclusive, ih]
    cases flip <;> cases seed <;> simp [hsum, pow_succ] <;> ring

/-- The decision event for the fixed repeated probe, with a fair Boolean seed. -/
def allPlusGHZAccept (m : ℕ) : Finset (Bool × Transcript (Option Bool) m) :=
  Finset.univ.filter fun t => ghzGuess t.1 t.2 = true

private theorem allPlusGHZ_seeded_success (flip : Bool) (m : ℕ) :
    (∑ t : Bool × Transcript (Option Bool) m, if ghzGuess t.1 t.2 = flip
      then seededLaw (probeKernel flip) (fun _ => 1 / 2) (fun _ => allPlusGHZPolicy ι m) t else 0) =
      1 - (1 - conclusiveMass ι) ^ m / 2 := by
  rw [Fintype.sum_prod_type]
  have h (seed : Bool) :
      (∑ t : Transcript (Option Bool) m, if ghzGuess seed t = flip
        then seededLaw (probeKernel flip) (fun _ => 1 / 2) (fun _ => allPlusGHZPolicy ι m)
          (seed, t) else 0) =
        (1 / 2 : ℝ) * (1 - (1 - conclusiveMass ι) ^ m * (if seed = flip then 0 else 1)) := by
    rw [← allPlusGHZPolicy_success flip seed m, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    split <;> simp_all [seededLaw, jointLaw]
  calc
    _ = ∑ seed : Bool, (1 / 2 : ℝ) *
        (1 - (1 - conclusiveMass ι) ^ m * (if seed = flip then 0 else 1)) :=
      Finset.sum_congr rfl (fun seed _ => h seed)
    _ = _ := by
      rw [Fintype.sum_bool]
      cases flip <;> simp <;> ring

open Classical in
/-- The all-plus GHZ protocol attains the sharp curve on each of the two channels. -/
theorem liu_wild_product_input_success_attained (M : ℕ) :
    (∑ t ∈ (allPlusGHZAccept M)ᶜ,
      seededLaw (probeKernel false) (fun _ => 1 / 2) (fun _ => allPlusGHZPolicy ι M) t) =
        1 - (1 - conclusiveMass ι) ^ M / 2 ∧
    (∑ t ∈ allPlusGHZAccept M,
      seededLaw (probeKernel true) (fun _ => 1 / 2) (fun _ => allPlusGHZPolicy ι M) t) =
        1 - (1 - conclusiveMass ι) ^ M / 2 := by
  have hcompl : (allPlusGHZAccept M)ᶜ =
      Finset.univ.filter (fun t : Bool × Transcript (Option Bool) M =>
        ghzGuess t.1 t.2 = false) := by
    ext t
    simp [allPlusGHZAccept]
  constructor
  · rw [hcompl, Finset.sum_filter]
    exact allPlusGHZ_seeded_success false M
  · simp only [allPlusGHZAccept, Finset.sum_filter]
    exact allPlusGHZ_seeded_success true M

end NonemptyRegister

/-- The original GHZ witness applies to the same pair once the register has at least two sites.
The pair has minimum Kraus count two and is unital. -/
theorem rank_two_pair_with_coherent_witness [Nontrivial ι] :
    (∀ flip, IsLeast {k | HasKrausCount (channel (ι := ι) flip) k} 2 ∧
      (channel (ι := ι) flip).toCompletelyPositiveMap 1 = 1) ∧
    (∀ flip, referenceState (channel (ι := ι) flip)
      (ghzState zeroWord oneWord words_ne false) = ghzState zeroWord oneWord words_ne flip) ∧
    diamondDistance (channel (ι := ι) false) (channel true) = 2 :=
  ⟨rank_two_ambiguity.1, fun flip => ghz_output _ _ words_ne flip, maximal_diamond⟩

end UnitaryReconstruction.LiuWildProductProbes
