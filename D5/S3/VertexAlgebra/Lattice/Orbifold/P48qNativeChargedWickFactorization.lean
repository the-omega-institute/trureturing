/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeChargedWickFactorization
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Factor the native charged source coefficient into its Wick field terms. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCreationWordExpansion
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedDiagonalWickScalar

/-! The Wick factorization of the native charged source coefficient. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeChargedWickFactorization

open LatticeGeneratingFieldLocality (Charge creationExponential)
open P48qTwistedChargeAction (lattice g Momentum)
open P48qThirdTwistedField (Cartan Fock State chargeVector integratedJetMean integratedJetPair)
open P48qTwistedHeisenberg (project projectAt projectAt_eq_fourier)
open ThirdEigenspacePairing (p48qForm)
open P48qJetContractions (pairJetCoeff)
open P48qAllJetWickField (Jet oscillatorJet totalLevel totalLevel_perm leafShift
  singletonWeight pairWeight pairWeight_swap allJetCoeff nativePolynomialField)
open P48qJetNormalOrdering (normalOrderedCoeff normalOrderedCoeff_perm)
open P48qNativeCreationWordExpansion (Letter letterIndex letterLevel letterWeight
  word wordLevel wordWeight totalLevel_word nativePolynomialField_creationExponential_coeff)
open P48qFiniteWickSum (wickSeries retainedSeries singletonPrimitive pairPrimitive)
open P48qArbitraryWickRecursion (normalWick normalWickWord normalWick_nil normalWick_step)
open PowerSeries (C X coeff constantCoeff)
open Finset.HasAntidiagonal (antidiagonal)

local notation "shift" => ThirdTwistedChargeAction.shift lattice g
local notation "pairMatrix" => (Matrix.of fun x y : Jet => pairWeight x y)

/-- The current jet of a native oscillator letter. -/
def letterJet {d : ℕ} (j : Letter d) : Jet := oscillatorJet (letterIndex j)

/-- The source weight of one native oscillator letter, in its positive degree. -/
def letterSeries {d : ℕ} (a : Charge lattice) (j : Letter d) : PowerSeries Fock :=
  letterWeight a j • X ^ letterLevel j

/-- Read a retained jet word at physical cover exponent `h`, with its source
level removed from the normal-ordered coefficient index. -/
def retainedJetCoeff (c : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock)
    (xs : List Jet) : Fock :=
  (normalOrderedCoeff c (h - 3 * (totalLevel xs : ℤ)) xs (Finsupp.single p P)) (shift c p)

/-- The factorial-weighted series of the actual retained jet coefficients. -/
def nativeRetainedSeries (a b : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock)
    (d : ℕ) : PowerSeries Fock :=
  retainedSeries (letterJet (d := d)) (letterSeries a) (retainedJetCoeff (a + b) h p P) []

private theorem constantCoeff_letterSeries {d : ℕ} (a : Charge lattice) (j : Letter d) :
    constantCoeff (letterSeries a j) = 0 := by
  simp [letterSeries, letterLevel, pow_succ]

private theorem retainedJetCoeff_perm (c : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock)
    {xs ys : List Jet} (hperm : xs.Perm ys) :
    retainedJetCoeff c h p P xs = retainedJetCoeff c h p P ys := by
  unfold retainedJetCoeff
  rw [totalLevel_perm hperm, normalOrderedCoeff_perm c _ hperm]

private def evalAt (w : State) (q : Momentum) : Module.End ℂ State →ₗ[ℂ] Fock :=
  (Finsupp.lapply q).comp (LinearMap.applyₗ (R := ℂ) w)

private theorem map_normalWick (L : Module.End ℂ State →ₗ[ℂ] Fock)
    (A : Matrix Jet Jet ℂ) (μ : Jet → ℂ) (N : List Jet → Module.End ℂ State)
    (pending kept : List Jet) :
    L (normalWick A μ N pending kept) =
      normalWick A μ (fun xs => L (N xs)) pending kept := by
  cases pending with
  | nil => simp only [normalWick_nil]
  | cons x xs =>
    rw [normalWick_step, normalWick_step]
    simp only [map_add, map_smul, map_sum]
    rw [map_normalWick L A μ N xs (kept ++ [x]), map_normalWick L A μ N xs kept]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [map_normalWick L A μ N (xs.eraseIdx j) kept]
termination_by pending.length
decreasing_by
  all_goals
    simp only [List.length_cons]
    first | exact Nat.lt_succ_self _ | exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..)

private theorem eval_allJetCoeff (c : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock)
    (d : ℕ) (xs : List Jet) (hx : totalLevel xs = d) :
    evalAt (Finsupp.single p P) (shift c p) (allJetCoeff c (h - 3 * (d : ℤ)) xs) =
      normalWick pairMatrix (singletonWeight c) (retainedJetCoeff c h p P) xs [] := by
  have hleaf :
      (fun kept => evalAt (Finsupp.single p P) (shift c p)
        (normalOrderedCoeff c (h - 3 * (d : ℤ) + leafShift xs kept) kept)) =
        retainedJetCoeff c h p P := by
    funext kept
    have hshift : h - 3 * (d : ℤ) + leafShift xs kept = h - 3 * (totalLevel kept : ℤ) := by
      rw [leafShift, hx]
      ring
    rw [hshift]
    rfl
  rw [allJetCoeff, normalWickWord, map_normalWick, hleaf]

private theorem coeff_weight_mul_C {d m : ℕ} (a : Charge lattice) (f : Fin m → Letter d)
    (v : Fock) :
    coeff d (P48qFiniteWickSum.weight (letterSeries a) f * C v) =
      if wordLevel f = d then wordWeight a f • v else 0 := by
  rw [P48qFiniteWickSum.weight, PowerSeries.coeff_mul_C]
  simp only [letterSeries, Finset.prod_smul, Finset.prod_pow_eq_pow_sum, PowerSeries.coeff_smul,
    PowerSeries.coeff_X_pow]
  change (wordWeight a f • (if d = wordLevel f then (1 : Fock) else 0)) * v = _
  by_cases heq : wordLevel f = d
  · rw [ite_eq_left heq.symm, ite_eq_left heq, smul_mul_assoc, one_mul]
  · rw [ite_eq_right (Ne.symm heq), ite_eq_right heq, smul_zero, zero_mul]

private theorem nativeCoeff_eq_wickSeries (a c : Charge lattice) (h : ℤ) (p : Momentum)
    (P : Fock) (d : ℕ) :
    (HVertexOperator.coeff (nativePolynomialField c
      (coeff d (creationExponential lattice a))) (h - 3 * (d : ℤ)) (Finsupp.single p P))
      (shift c p) =
    coeff d (wickSeries (letterJet (d := d)) (letterSeries a) pairMatrix (singletonWeight c)
      (retainedJetCoeff c h p P) []) := by
  classical
  change evalAt (Finsupp.single p P) (shift c p)
    (HVertexOperator.coeff (nativePolynomialField c
      (coeff d (creationExponential lattice a))) (h - 3 * (d : ℤ))) = _
  rw [nativePolynomialField_creationExponential_coeff, wickSeries, P48qFiniteWickSum.wordSeries,
    P48qFiniteWickSum.coeff_sumByDegree]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro m _
  change _ = coeff d (algebraMap ℂ (PowerSeries Fock) ((m.factorial : ℂ)⁻¹) *
    ∑ f : Fin m → Letter d, P48qFiniteWickSum.weight (letterSeries a) f *
      C (normalWick pairMatrix (singletonWeight c) (retainedJetCoeff c h p P)
        (P48qFiniteWickSum.word letterJet f) []))
  rw [PowerSeries.algebraMap_apply, PowerSeries.coeff_C_mul, ← Algebra.smul_def]
  congr 1
  simp only [map_sum, coeff_weight_mul_C, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro f _
  split_ifs with hf
  · rw [eval_allJetCoeff c h p P d _ ((totalLevel_word f).trans hf)]
    simp only [word, P48qFiniteWickSum.word, List.map_ofFn, letterJet]
    rfl
  · rfl

/-- The native charged coefficient factors into the exponential of the finite
singleton and half-pair series times the actual retained series. -/
theorem nativePolynomialField_coeff_eq_wick_factorization (a b : Charge lattice)
    (h : ℤ) (p : Momentum) (P : Fock) (d : ℕ) :
    (HVertexOperator.coeff (nativePolynomialField (a + b)
      (coeff d (creationExponential lattice a))) (h - 3 * (d : ℤ)) (Finsupp.single p P))
      (shift (a + b) p) =
    coeff d ((PowerSeries.exp Fock).subst
      (singletonPrimitive (letterJet (d := d)) (letterSeries a) (singletonWeight (a + b)) +
        (1 / 2 : ℂ) • pairPrimitive (letterJet (d := d)) (letterSeries a) pairMatrix) *
      nativeRetainedSeries a b h p P d) := by
  rw [nativeCoeff_eq_wickSeries, nativeRetainedSeries,
    P48qFiniteWickSum.wickSeries_eq_exp_mul_retainedSeries (letterJet (d := d)) _ pairMatrix _ _
      (constantCoeff_letterSeries a) pairWeight_swap (retainedJetCoeff_perm (a + b) h p P)]

#print axioms nativePolynomialField_coeff_eq_wick_factorization

private def projectLinear (k : ℤ) : Cartan →ₗ[ℂ] Cartan where
  toFun := projectAt k
  map_add' u v := by
    simp only [projectAt_eq_fourier, project, map_add, smul_add]
    abel
  map_smul' r u := by
    simp only [projectAt_eq_fourier, project, map_smul, RingHom.id_apply, smul_add, smul_comm r]

private def singletonLinear (c : Charge lattice) (n : ℕ+) : Cartan →ₗ[ℂ] ℂ :=
  ∑ r ∈ Finset.range 3, Ring.choose (-((r : ℂ) / 3)) (n : ℕ) •
    (p48qForm.flip (chargeVector c)).comp (projectLinear r)

private theorem singletonLinear_apply (c : Charge lattice) (x : Jet) :
    singletonLinear c x.2 x.1 = singletonWeight c x := by
  simp [singletonLinear, singletonWeight, projectLinear, smul_eq_mul]

private def pairLinear (n : ℕ+) (y : Jet) : Cartan →ₗ[ℂ] ℂ :=
  pairJetCoeff (1 / 3 : ℂ) (n : ℕ) (y.2 : ℕ) •
      (p48qForm.flip (projectAt 2 y.1)).comp (projectLinear 1) +
    pairJetCoeff (2 / 3 : ℂ) (n : ℕ) (y.2 : ℕ) •
      (p48qForm.flip (projectAt 1 y.1)).comp (projectLinear 2)

private theorem pairLinear_apply (x y : Jet) :
    pairLinear x.2 y x.1 = pairWeight x y := by
  simp [pairLinear, pairWeight, projectLinear, smul_eq_mul]

private def letterScalar {d : ℕ} (a : Charge lattice) (n : ℕ) (j : Letter d) : ℂ :=
  if n = letterLevel j then letterWeight a j else 0

private theorem coeff_letterSeries {d : ℕ} (a : Charge lattice) (n : ℕ) (j : Letter d) :
    coeff n (letterSeries a j) = algebraMap ℂ Fock (letterScalar a n j) := by
  simp only [letterSeries, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, letterScalar]
  split_ifs <;> simp [Algebra.smul_def]

private theorem sum_chargeCoordinates (a : Charge lattice) :
    (∑ i : Fin lattice.rank, (a i : ℂ) • Pi.single i (1 : ℂ)) = chargeVector a := by
  classical
  funext i
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp [chargeVector]
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji.symm]
  · simp

private theorem sum_letterKernel (a : Charge lattice) (d n : ℕ) (hn : n ≤ d)
    (L : ℕ+ → Cartan →ₗ[ℂ] ℂ) :
    (∑ j : Letter d, L (letterJet j).2 (letterJet j).1 * letterScalar a n j) =
      if hp : 0 < n then L ⟨n, hp⟩ (chargeVector a) / (n : ℂ) else 0 := by
  classical
  by_cases hp : 0 < n
  · let k : Fin d := ⟨n - 1, by omega⟩
    have hk : k.val + 1 = n := by dsimp [k]; omega
    rw [dite_eq_left hp, Fintype.sum_prod_type_right, Finset.sum_eq_single k]
    · have hlevel (i : Fin lattice.rank) : (letterJet (i, k)).2 = ⟨n, hp⟩ :=
        Subtype.ext hk
      simp only [letterScalar, letterLevel, hk, ite_true, letterWeight, hlevel]
      change (∑ i : Fin lattice.rank, L ⟨n, hp⟩ (Pi.single i 1) *
        ((a i : ℂ) / (n : ℂ))) = _
      simp only [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
      congr 1
      rw [← sum_chargeCoordinates, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, smul_eq_mul, mul_comm]
    · intro l _ hl
      have hne : n ≠ l.val + 1 := fun h => hl (Fin.ext (by omega))
      simp [letterScalar, letterLevel, hne]
    · simp
  · have hz : n = 0 := by omega
    subst n
    simp [letterScalar, letterLevel]

private theorem coeff_singletonPrimitive (a c : Charge lattice) (d n : ℕ) (hn : n ≤ d) :
    coeff n (singletonPrimitive (letterJet (d := d)) (letterSeries a) (singletonWeight c)) =
      algebraMap ℂ Fock (coeff n (integratedJetMean a c)) := by
  simp only [singletonPrimitive, map_sum, PowerSeries.coeff_smul, coeff_letterSeries]
  simp only [Algebra.smul_def, ← map_mul, ← map_sum, ← singletonLinear_apply]
  rw [sum_letterKernel a d n hn, integratedJetMean, PowerSeries.coeff_mk]
  split_ifs with hp
  · rw [show singletonLinear c ⟨n, hp⟩ (chargeVector a) =
      singletonWeight c (chargeVector a, ⟨n, hp⟩)
      from singletonLinear_apply c (chargeVector a, ⟨n, hp⟩)]
  · rfl

private theorem pair_sum_at_degrees (a : Charge lattice) (d m n : ℕ)
    (hm : m ≤ d) (hn : n ≤ d) :
    (∑ x : Letter d, ∑ y : Letter d,
      pairWeight (letterJet x) (letterJet y) * (letterScalar a m x * letterScalar a n y)) =
      if hp : 0 < m ∧ 0 < n then
        pairWeight (chargeVector a, ⟨m, hp.1⟩) (chargeVector a, ⟨n, hp.2⟩) /
          ((m : ℂ) * (n : ℂ))
      else 0 := by
  have hrow (x : Letter d) :
      (∑ y : Letter d, pairWeight (letterJet x) (letterJet y) * letterScalar a n y) =
        if hp : 0 < n then
          pairWeight (chargeVector a, ⟨n, hp⟩) (letterJet x) / (n : ℂ)
        else 0 := by
    simp_rw [fun y : Letter d => pairWeight_swap (letterJet x) (letterJet y),
      ← pairLinear_apply]
    exact sum_letterKernel a d n hn (fun l => pairLinear l (letterJet x))
  simp_rw [mul_left_comm _ (letterScalar a m _), ← Finset.mul_sum, hrow]
  by_cases hp : 0 < n
  · let y : Jet := (chargeVector a, ⟨n, hp⟩)
    simp only [dite_eq_left hp]
    change (∑ x : Letter d, letterScalar a m x * (pairWeight y (letterJet x) / (n : ℂ))) = _
    have hcol :
        (∑ x : Letter d, pairWeight (letterJet x) y * letterScalar a m x) =
          if h : 0 < m then pairWeight (chargeVector a, ⟨m, h⟩) y / (m : ℂ) else 0 := by
      simp_rw [← pairLinear_apply]
      exact sum_letterKernel a d m hm (fun l => pairLinear l y)
    simp_rw [pairWeight_swap y, div_eq_mul_inv, ← mul_assoc,
      mul_comm (letterScalar a m _), ← Finset.sum_mul, ← div_eq_mul_inv, hcol]
    by_cases hm' : 0 < m
    · rw [dite_eq_left hm', dite_eq_left ⟨hm', hp⟩, div_div]
    · simp [hm']
  · simp [hp]

private theorem coeff_pairPrimitive (a : Charge lattice) (d n : ℕ) (hn : n ≤ d) :
    coeff n (pairPrimitive (letterJet (d := d)) (letterSeries a) pairMatrix) =
      algebraMap ℂ Fock (coeff n (integratedJetPair a)) := by
  simp only [P48qFiniteWickSum.pairPrimitive_eq_sum, map_sum, PowerSeries.coeff_smul]
  simp only [PowerSeries.coeff_mul, coeff_letterSeries, Matrix.of_apply, Algebra.smul_def,
    Finset.mul_sum]
  simp only [← map_mul, ← map_sum]
  rw [integratedJetPair, PowerSeries.coeff_mk]
  congr 1
  simp only [Finset.sum_comm (s := (Finset.univ : Finset (Letter d))) (t := antidiagonal n)]
  apply Finset.sum_congr rfl
  intro v hv
  have hv' := Finset.HasAntidiagonal.mem_antidiagonal.mp hv
  exact pair_sum_at_degrees a d v.1 v.2 (by omega) (by omega)

private theorem coeff_subst_mul_of_coeff_eq (d : ℕ) (E S T R : PowerSeries Fock)
    (hS : constantCoeff S = 0)
    (h : ∀ n ≤ d, coeff n S = coeff n T) :
    coeff d (E.subst S * R) = coeff d (E.subst T * R) := by
  have hp (m n : ℕ) (hn : n ≤ d) : coeff n (S ^ m) = coeff n (T ^ m) := by
    induction m generalizing n with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro v hv
      have hv' := Finset.HasAntidiagonal.mem_antidiagonal.mp hv
      rw [ih v.1 (by omega), h v.2 (by omega)]
  have hT : constantCoeff T = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply, hS] using
      (h 0 (Nat.zero_le d)).symm
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro v hv
  have hv' := Finset.HasAntidiagonal.mem_antidiagonal.mp hv
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hS),
    PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hT)]
  simp only [hp _ _ (show v.1 ≤ d by omega)]

/-- Through the source degree being read, the finite Wick exponential agrees
with the exponential of the all-degree integrated singleton and half-pair kernels. -/
theorem nativePolynomialField_coeff_eq_integrated_wick_factorization (a b : Charge lattice)
    (h : ℤ) (p : Momentum) (P : Fock) (d : ℕ) :
    (HVertexOperator.coeff (nativePolynomialField (a + b)
      (coeff d (creationExponential lattice a))) (h - 3 * (d : ℤ)) (Finsupp.single p P))
      (shift (a + b) p) =
    coeff d ((PowerSeries.exp Fock).subst
      (PowerSeries.map (algebraMap ℂ Fock)
        (integratedJetMean a (a + b) + (1 / 2 : ℂ) • integratedJetPair a)) *
      nativeRetainedSeries a b h p P d) := by
  rw [nativePolynomialField_coeff_eq_wick_factorization]
  apply coeff_subst_mul_of_coeff_eq
  · simp [singletonPrimitive, P48qFiniteWickSum.pairPrimitive_eq_sum, constantCoeff_letterSeries]
  · intro n hn
    simp only [map_add, PowerSeries.coeff_smul, coeff_singletonPrimitive a (a + b) d n hn,
      coeff_pairPrimitive a d n hn, PowerSeries.coeff_map]
    simp only [smul_eq_mul, Algebra.smul_def, ← map_mul]

#print axioms nativePolynomialField_coeff_eq_integrated_wick_factorization

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeChargedWickFactorization
