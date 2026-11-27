/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeMonodromy
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The standard lift implements cover monodromy on the native Wick field. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qAllJetWickField
import D5.S3.VertexAlgebra.Lattice.Orbifold.NativeStandardThirdLift
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedGeneratorVacuum
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeChargedWickFactorization

/-! Cover monodromy of the native order-three Wick field under the standard lift. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeMonodromy

open LatticeGeneratingFieldLocality (Charge)
open P48qTwistedChargeAction (lattice g g_cube g_isometry liftPhase)
open P48qThirdTwistedField (Cartan State chargeVector concreteChargedField)
open ThirdEigenspacePairing (p48qAction p48qForm)
open P48qTwistedHeisenberg (projectAt projectAt_eq_fourier project mode modeLinear currentField)
open P48qTwistedGeneratorVacuum (mode_action rotateCover rotateCover_coeff concreteChargedField_g)
open P48qSignedNormalWord (Indices insertMode insertMode_apply)
open P48qJetNormalOrdering (jetWeight jetTerm jetTerm_cons jetTerm_finite
  normalOrderedCoeff normalOrderedCoeff_cons_apply normalOrderedField_coeff normalOrderedField_nil)
open P48qAllJetWickField
open P48qArbitraryWickRecursion (normalWick normalWickWord normalWick_nil normalWick_step)

open private formInvariant action_chargeVector from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
open private zeta_zpow_add_three_mul from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedGeneratorVacuum

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "η" => liftPhase.eta
local notation "pairMatrix" => (Matrix.of fun p q : Jet => pairWeight p q)

private def actJet (p : Jet) : Jet := (p48qAction p.1, p.2)

private theorem projectAt_action_comm (r : ℤ) (u : Cartan) :
    projectAt r (p48qAction u) = p48qAction (projectAt r u) := by
  simp only [projectAt_eq_fourier, project, map_add, map_smul]

private theorem singletonWeight_action (a : Charge lattice) (p : Jet) :
    singletonWeight (g a) (actJet p) = singletonWeight a p := by
  simp only [singletonWeight, actJet, projectAt_action_comm, ← action_chargeVector, formInvariant]

private theorem pairWeight_action (p q : Jet) :
    pairWeight (actJet p) (actJet q) = pairWeight p q := by
  simp only [pairWeight, actJet, projectAt_action_comm, formInvariant]

private theorem totalLevel_action (jets : List Jet) :
    totalLevel (jets.map actJet) = totalLevel jets := by
  induction jets with
  | nil => rfl
  | cons p tail ih => simp only [List.map_cons, totalLevel, actJet, ih]

private theorem insertMode_action (u : Cartan) (m : ℤ) (B : Module.End ℂ State) :
    insertMode (p48qAction u, m) B = ζ ^ (-m) • insertMode (u, m) B := by
  simp only [insertMode_apply, mode_action]
  split <;> simp only [smul_mul_assoc, mul_smul_comm]

private theorem normalOrderedCoeff_action (a : Charge lattice) (k : ℤ) (jets : List Jet) :
    (↑((η a)⁻¹) : ℂ) • normalOrderedCoeff (g a) k (jets.map actJet) =
      ζ ^ k • normalOrderedCoeff a k jets := by
  induction jets generalizing k with
  | nil =>
    rw [List.map_nil, ← normalOrderedField_coeff, ← normalOrderedField_coeff,
      normalOrderedField_nil, normalOrderedField_nil]
    have h := congrArg (fun A : VertexOperator ℂ State => HVertexOperator.coeff A k)
      (concreteChargedField_g a)
    simpa only [map_smul, Pi.smul_apply, rotateCover_coeff] using h
  | cons p tail ih =>
    apply LinearMap.ext
    intro w
    simp only [LinearMap.smul_apply, List.map_cons, normalOrderedCoeff_cons_apply]
    rw [smul_finsum, smul_finsum]
    apply finsum_congr
    intro m
    let j : ℤ := k + 3 * ((p.2 : ℕ) : ℤ) + m
    change (↑((η a)⁻¹) : ℂ) • (jetWeight p.2 m •
      insertMode (p48qAction p.1, m) (normalOrderedCoeff (g a) j (tail.map actJet)) w) =
        ζ ^ k • (jetWeight p.2 m • insertMode (p.1, m) (normalOrderedCoeff a j tail) w)
    rw [smul_comm (↑((η a)⁻¹) : ℂ) (jetWeight p.2 m),
      smul_comm (ζ ^ k) (jetWeight p.2 m)]
    apply congrArg (fun x : State => jetWeight p.2 m • x)
    have hinsert :
        (↑((η a)⁻¹) : ℂ) • insertMode (p48qAction p.1, m)
          (normalOrderedCoeff (g a) j (tail.map actJet)) =
          ζ ^ k • insertMode (p.1, m) (normalOrderedCoeff a j tail) := by
      rw [← (insertMode (p48qAction p.1, m)).map_smul, ih j, map_smul,
        insertMode_action, smul_smul, ← zpow_add₀ (Units.ne_zero ThirdTwistedChargeCocycle.zeta),
        show j + -m = k + 3 * ((p.2 : ℕ) : ℤ) by dsimp [j]; omega,
        zeta_zpow_add_three_mul]
    exact congrArg (fun B : Module.End ℂ State => B w) hinsert

private theorem normalWick_action (a : Charge lattice) (k : ℤ) (level : ℕ)
    (pending kept : List Jet) :
    (↑((η a)⁻¹) : ℂ) • normalWick pairMatrix (singletonWeight (g a))
      (fun xs => normalOrderedCoeff (g a) (k + 3 * ((level : ℤ) - totalLevel xs)) xs)
      (pending.map actJet) (kept.map actJet) =
    ζ ^ k • normalWick pairMatrix (singletonWeight a)
      (fun xs => normalOrderedCoeff a (k + 3 * ((level : ℤ) - totalLevel xs)) xs)
      pending kept := by
  cases pending with
  | nil =>
    simp only [List.map_nil, normalWick_nil, totalLevel_action,
      normalOrderedCoeff_action, zeta_zpow_add_three_mul]
  | cons p tail =>
    simp only [List.map_cons, normalWick_step, smul_add, Finset.smul_sum, singletonWeight_action]
    rw [show kept.map actJet ++ [actJet p] = (kept ++ [p]).map actJet by
      simp only [List.map_append, List.map_cons, List.map_nil],
      normalWick_action a k level tail (kept ++ [p])]
    rw [smul_comm (↑((η a)⁻¹) : ℂ) (singletonWeight a p),
      smul_comm (ζ ^ k) (singletonWeight a p), normalWick_action a k level tail kept]
    congr 1
    apply Fintype.sum_equiv (finCongr (List.length_map (f := actJet) (as := tail))) _ _
    intro j
    simp only [List.get_eq_getElem, List.getElem_map, finCongr_apply, Fin.val_cast,
      Matrix.of_apply, pairWeight_action, List.eraseIdx_map]
    rw [smul_comm (↑((η a)⁻¹) : ℂ) (pairWeight p tail[j.val]),
      smul_comm (ζ ^ k) (pairWeight p tail[j.val]),
      normalWick_action a k level (tail.eraseIdx j.val) kept]
termination_by pending.length
decreasing_by
  all_goals
    simp only [List.length_cons]
    first | exact Nat.lt_succ_self _ | exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..)

/-- Every finite jet word transforms with the charged ground phase and its
total Laurent cover exponent. -/
theorem allJetCoeff_action (a : Charge lattice) (k : ℤ) (jets : List Jet) :
    (↑((η a)⁻¹) : ℂ) • allJetCoeff (g a) k (jets.map actJet) =
      ζ ^ k • allJetCoeff a k jets := by
  simpa only [allJetCoeff, normalWickWord, leafShift, totalLevel_action, List.map_nil]
    using normalWick_action a k (totalLevel jets) jets []

#print axioms allJetCoeff_action

private def normalHeadLinear (a : Charge lattice) (k : ℤ) (d : ℕ+) (tail : List Jet) :
    Cartan →ₗ[ℂ] Module.End ℂ State where
  toFun u := normalOrderedCoeff a k ((u, d) :: tail)
  map_add' u v := by
    apply LinearMap.ext
    intro w
    let f (u : Cartan) (i : ℤ × Indices (tail.map Prod.fst).length) :=
      jetTerm a k ((u, d) :: tail) i w
    change (∑ᶠ i, f (u + v) i) = (∑ᶠ i, f u i) + ∑ᶠ i, f v i
    have hfinite (x : Cartan) : Function.HasFiniteSupport (f x) :=
      jetTerm_finite a k ((x, d) :: tail) w
    rw [← finsum_add_distrib (hfinite u) (hfinite v)]
    apply finsum_congr
    rintro ⟨m, rest⟩
    simp only [f, jetTerm_cons, insertMode_apply]
    have hm : mode (u + v) m = mode u m + mode v m := (modeLinear m).map_add u v
    simp only [hm, add_mul, mul_add, LinearMap.smul_apply]
    by_cases hm' : m < 0
    · simp only [ite_eq_left hm', smul_add, LinearMap.add_apply]
    · simp only [ite_eq_right hm', smul_add, LinearMap.add_apply]
  map_smul' c u := by
    apply LinearMap.ext
    intro w
    change (∑ᶠ i, jetTerm a k ((c • u, d) :: tail) i w) =
      c • ∑ᶠ i, jetTerm a k ((u, d) :: tail) i w
    rw [smul_finsum]
    apply finsum_congr
    rintro ⟨m, rest⟩
    have hm : mode (c • u) m = c • mode u m := (modeLinear m).map_smul c u
    simp only [jetTerm_cons, insertMode_apply, hm, smul_mul_assoc, mul_smul_comm,
      LinearMap.smul_apply]
    split <;> simp_all only [LinearMap.smul_apply, smul_comm c]

open private singletonLinear singletonLinear_apply pairLinear pairLinear_apply
  from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeChargedWickFactorization

private theorem normalWick_keptHead (a : Charge lattice) (k : ℤ) (level : ℕ)
    (d : ℕ+) (u : Cartan) (pending kept : List Jet) :
    (normalWick pairMatrix (singletonWeight a)
      (fun xs => normalHeadLinear a (k + 3 * ((level : ℤ) - (d : ℕ) - totalLevel xs)) d xs)
      pending kept) u =
    normalWick pairMatrix (singletonWeight a)
      (fun xs => normalOrderedCoeff a (k + 3 * ((level : ℤ) - totalLevel xs)) xs)
      pending ((u, d) :: kept) := by
  cases pending with
  | nil =>
    simp only [normalWick_nil, totalLevel]
    change normalOrderedCoeff a (k + 3 * ((level : ℤ) - (d : ℕ) - totalLevel kept))
        ((u, d) :: kept) = _
    congr 1
    push_cast
    ring
  | cons p tail =>
    simp only [normalWick_step, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      List.cons_append]
    rw [normalWick_keptHead a k level d u tail (kept ++ [p]),
      normalWick_keptHead a k level d u tail kept]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [normalWick_keptHead a k level d u (tail.eraseIdx j) kept]
termination_by pending.length
decreasing_by
  all_goals
    simp only [List.length_cons]
    first | exact Nat.lt_succ_self _ | exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..)

private def allJetHeadLinear (a : Charge lattice) (k : ℤ) (d : ℕ+) (tail : List Jet) :
    Cartan →ₗ[ℂ] Module.End ℂ State :=
  let level := (d : ℕ) + totalLevel tail
  let leaf (xs : List Jet) := normalOrderedCoeff a (k + 3 * ((level : ℤ) - totalLevel xs)) xs
  normalWick pairMatrix (singletonWeight a)
      (fun xs => normalHeadLinear a (k + 3 * ((level : ℤ) - (d : ℕ) - totalLevel xs)) d xs)
      tail [] +
    (singletonLinear a d).smulRight (normalWick pairMatrix (singletonWeight a) leaf tail []) +
    ∑ j : Fin tail.length, (pairLinear d (tail.get j)).smulRight
      (normalWick pairMatrix (singletonWeight a) leaf (tail.eraseIdx j) [])

private theorem allJetHeadLinear_apply (a : Charge lattice) (k : ℤ)
    (d : ℕ+) (tail : List Jet) (u : Cartan) :
    allJetHeadLinear a k d tail u = allJetCoeff a k ((u, d) :: tail) := by
  simp only [allJetHeadLinear, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
    normalWick_keptHead, allJetCoeff, normalWickWord, normalWick_step, List.nil_append, leafShift,
    totalLevel, Matrix.of_apply, ← singletonLinear_apply a (u, d), ← pairLinear_apply (u, d)]

private def jetPolynomial (d : ℕ+) (u : Cartan) : NativePolynomial :=
  ∑ i : Fin lattice.rank, u i • MvPolynomial.X (i, (d : ℕ) - 1)

private def jetWordPolynomial (jets : List Jet) : NativePolynomial :=
  (jets.map fun p => jetPolynomial p.2 p.1).prod

private theorem jetPolynomial_oscillatorJet (j : NativeIndex) :
    jetPolynomial (oscillatorJet j).2 (oscillatorJet j).1 = MvPolynomial.X j := by
  classical
  obtain ⟨i, n⟩ := j
  simp [jetPolynomial, oscillatorJet, Pi.single_apply]

private def nativeCoeff (a : Charge lattice) (k : ℤ) :
    NativePolynomial →ₗ[ℂ] Module.End ℂ State :=
  ((LinearMap.proj k).comp HVertexOperator.coeff).comp
    (nativeField.comp (Finsupp.lsingle a))

private theorem nativeCoeff_word (a : Charge lattice) (k : ℤ) (word : List NativeIndex) :
    nativeCoeff a k (nativeWordPolynomial word) = allJetCoeff a k (word.map oscillatorJet) := by
  simp only [nativeCoeff, LinearMap.comp_apply, LinearMap.proj_apply, Finsupp.lsingle_apply,
    nativeField_word, allJetField_coeff]

private theorem nativeCoeff_jetWord (a : Charge lattice) (k : ℤ)
    (jets : List Jet) (word : List NativeIndex) :
    nativeCoeff a k (jetWordPolynomial jets * nativeWordPolynomial word) =
      allJetCoeff a k (jets ++ word.map oscillatorJet) := by
  induction jets generalizing word with
  | nil =>
    simpa only [jetWordPolynomial, List.map_nil, List.prod_nil, one_mul, List.nil_append]
      using nativeCoeff_word a k word
  | cons p tail ih =>
    have hp : (p.2 : ℕ) - 1 + 1 = (p.2 : ℕ) := Nat.sub_add_cancel p.2.pos
    have hlevel (i : Fin lattice.rank) :
        oscillatorJet (i, (p.2 : ℕ) - 1) = (Pi.single i 1, p.2) :=
      Prod.ext rfl (Subtype.ext hp)
    have hdir : (∑ i : Fin lattice.rank, p.1 i • Pi.single i (1 : ℂ)) = p.1 := by
      classical
      ext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [Pi.single_eq_of_ne hij.symm]
      · simp
    change nativeCoeff a k
      (jetPolynomial p.2 p.1 * jetWordPolynomial tail * nativeWordPolynomial word) =
      allJetCoeff a k (p :: (tail ++ word.map oscillatorJet))
    rw [jetPolynomial, Finset.sum_mul, Finset.sum_mul, map_sum, ← allJetHeadLinear_apply]
    conv_rhs => rw [← hdir, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_mul_assoc, smul_mul_assoc, map_smul, map_smul, allJetHeadLinear_apply]
    apply congrArg (fun B : Module.End ℂ State => p.1 i • B)
    let j : NativeIndex := (i, (p.2 : ℕ) - 1)
    have hprod : MvPolynomial.X j * jetWordPolynomial tail * nativeWordPolynomial word =
        jetWordPolynomial tail * nativeWordPolynomial (j :: word) := by
      change _ = _ * (MvPolynomial.X j * nativeWordPolynomial word)
      ac_rfl
    rw [hprod, ih (j :: word)]
    apply allJetCoeff_perm
    simp only [List.map_cons, j, hlevel]
    cases p
    exact List.perm_middle

open private oscillator_X mixingMatrix from D5.S3.VertexAlgebra.Lattice.IsometryLift
open LatticeGeneratingFieldLocality (unitCharge)

private theorem oscillator_X_eq_jetPolynomial (j : NativeIndex) :
    IsometryLift.oscillator lattice g (MvPolynomial.X j) =
      jetPolynomial (oscillatorJet j).2 (p48qAction (oscillatorJet j).1) := by
  rw [oscillator_X, jetPolynomial]
  simp only [oscillatorJet]
  apply Finset.sum_congr rfl
  intro i _
  rw [mixingMatrix]
  have hunit : chargeVector (unitCharge lattice j.1) = Pi.single j.1 1 := by
    classical
    ext l
    simp [chargeVector, unitCharge, Pi.single_apply]
  rw [← hunit, action_chargeVector]
  rfl

private theorem oscillator_word (word : List NativeIndex) :
    IsometryLift.oscillator lattice g (nativeWordPolynomial word) =
      jetWordPolynomial ((word.map oscillatorJet).map actJet) := by
  induction word with
  | nil => simp [nativeWordPolynomial, jetWordPolynomial]
  | cons j tail ih =>
    change IsometryLift.oscillator lattice g (MvPolynomial.X j * nativeWordPolynomial tail) =
      jetPolynomial (oscillatorJet j).2 (p48qAction (oscillatorJet j).1) *
        jetWordPolynomial ((tail.map oscillatorJet).map actJet)
    rw [map_mul, oscillator_X_eq_jetPolynomial, ih]

open NativeStandardThirdLift (standardLift standardLift_single standardLift_ground_single)
open private nativeWordPolynomial_eq_monomial from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qAllJetWickField

local notation "σ" => standardLift lattice g g_cube g_isometry

private theorem eta_inv (a : Charge lattice) : (η a)⁻¹ = η a := by
  have hphase (b : Charge lattice) :
      (IsometryLift.phase lattice g b)⁻¹ = IsometryLift.phase lattice g b :=
    inv_eq_of_mul_eq_one_right (CyclicIsometryLift.phase_square lattice g g_isometry b)
  change (ThirdTwistedChargeAction.nativeStandardEta lattice g a)⁻¹ =
    ThirdTwistedChargeAction.nativeStandardEta lattice g a
  simp only [ThirdTwistedChargeAction.nativeStandardEta, hphase, mul_inv_rev, mul_comm]

private theorem nativeField_word_action (a : Charge lattice) (word : List NativeIndex) (k : ℤ) :
    HVertexOperator.coeff
        (nativeField (σ (Finsupp.single a (nativeWordPolynomial word)))) k =
      ζ ^ k •
        HVertexOperator.coeff (nativeField (Finsupp.single a (nativeWordPolynomial word))) k := by
  rw [standardLift_single, oscillator_word, map_smul, map_smul, Pi.smul_apply]
  change (↑(η a) : ℂ) • nativeCoeff (g a) k
      (jetWordPolynomial ((word.map oscillatorJet).map actJet)) =
      ζ ^ k • nativeCoeff a k (nativeWordPolynomial word)
  have h := nativeCoeff_jetWord (g a) k ((word.map oscillatorJet).map actJet) []
  simp only [nativeWordPolynomial, List.map_nil, List.prod_nil, mul_one, List.append_nil] at h
  rw [h, nativeCoeff_word]
  have hcov := allJetCoeff_action a k (word.map oscillatorJet)
  simpa only [eta_inv] using hcov

/-- BK (3.4) in Laurent cover coefficients, on every source and target state. -/
theorem nativeField_action_coeff (u : NativeStates) (k : ℤ) :
    HVertexOperator.coeff (nativeField (σ u)) k =
      ζ ^ k • HVertexOperator.coeff (nativeField u) k := by
  let read : NativeStates →ₗ[ℂ] Module.End ℂ State :=
    ((LinearMap.proj k).comp HVertexOperator.coeff).comp nativeField
  have h : read.comp (σ).toLinearMap = ζ ^ k • read := by
    apply Finsupp.lhom_ext
    intro a P
    change read (σ (Finsupp.single a P)) = ζ ^ k • read (Finsupp.single a P)
    induction P using MvPolynomial.induction_on' with
    | monomial e c =>
      classical
      have he : nativeWordPolynomial (oscillatorOccurrences e) = MvPolynomial.monomial e 1 := by
        rw [nativeWordPolynomial_eq_monomial, oscillatorOccurrences, Multiset.coe_toList,
          Finsupp.toMultiset_toFinsupp]
      rw [show MvPolynomial.monomial e c = c • nativeWordPolynomial (oscillatorOccurrences e) by
        rw [he, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      ]
      rw [← Finsupp.smul_single, map_smul, map_smul, map_smul, smul_comm (ζ ^ k) c]
      exact congrArg (fun B : Module.End ℂ State => c • B)
        (nativeField_word_action a (oscillatorOccurrences e) k)
    | add P Q ihP ihQ =>
      simp only [Finsupp.single_add, map_add, smul_add, ihP, ihQ]
  exact DFunLike.congr_fun h u

/-- The standard lift on the actual lattice carrier implements substitution
of `ζ x` for `x` in the actual native Hahn field. -/
theorem nativeField_monodromy (u : NativeStates) :
    nativeField (σ u) = rotateCover (nativeField u) := by
  apply HVertexOperator.coeff_inj
  funext k
  rw [rotateCover_coeff, nativeField_action_coeff]

#print axioms nativeField_action_coeff
#print axioms nativeField_monodromy

open ThirdTwistedIterate (currentAlong)
open P48qCurrentChargedIterate (chargedFirst contraction contraction_apply
  normalOrderedCurrentCoeff stateField stateField_first_coeff stateField_current)
open P48qJetNormalOrdering (normalOrderedCoeff_singleton_apply)
open P48qTwistedGeneratorVacuum (currentField_action)
open private currentPolynomial currentAlong_eq_polynomial from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField
open private chargeVector_zero from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedGeneratorVacuum

/-- The native first oscillator recovers the established neutral current. -/
theorem nativeField_current (v : Cartan) :
    nativeField (currentAlong lattice v) = currentField v := by
  apply HVertexOperator.coeff_inj
  funext k
  have hv := nativeCoeff_jetWord 0 k [(v, 1)] []
  change nativeCoeff 0 k (jetPolynomial 1 v * 1 * 1) = allJetCoeff 0 k [(v, 1)] at hv
  rw [mul_one, mul_one] at hv
  rw [currentAlong_eq_polynomial v]
  change nativeCoeff 0 k (jetPolynomial 1 v) = _
  rw [hv]
  have hcontra : contraction 0 v = 0 := by
    simp only [contraction_apply, chargeVector_zero, map_zero, mul_zero, add_zero]
  have hcurrent := stateField_first_coeff 0 v k
  change HVertexOperator.coeff (stateField (Finsupp.single 0 (currentPolynomial v))) k = _
    at hcurrent
  rw [← currentAlong_eq_polynomial v, stateField_current, hcontra, zero_smul, sub_zero] at hcurrent
  rw [hcurrent]
  have hs : k + leafShift [(v, (1 : ℕ+))] [(v, (1 : ℕ+))] = k := by
    simp only [leafShift, sub_self, mul_zero, add_zero]
  simp only [allJetCoeff, normalWickWord, normalWick_step, normalWick_nil, List.nil_append,
    singletonWeight_first, hcontra, neg_zero, zero_smul, List.length_nil, Fin.sum_univ_zero,
    add_zero, hs]
  apply LinearMap.ext
  intro w
  rw [normalOrderedCoeff_singleton_apply]
  simp only [jetWeight, PNat.val_ofNat, Nat.sub_self, Nat.cast_zero, mul_zero, add_zero,
    Ring.choose_zero_right, one_smul]
  rfl

example (a : Charge lattice) :
    nativeField (σ (Finsupp.single a 1)) = rotateCover (concreteChargedField a) := by
  rw [standardLift_ground_single, map_smul, nativeField_ground]
  change (↑(η a) : ℂ) • concreteChargedField (g a) = _
  rw [← eta_inv a, concreteChargedField_g]

example (i : Fin lattice.rank) :
    nativeField (σ (Finsupp.single 0 (MvPolynomial.X (i, 0)))) =
      rotateCover (currentField (Pi.single i 1)) := by
  have hzero : g (0 : Charge lattice) = 0 := map_zero _
  rw [standardLift_single, oscillator_X_eq_jetPolynomial, hzero,
    ThirdTwistedChargeAction.nativeStandardEta_fixed lattice g g_isometry 0 hzero,
    Units.val_one, one_smul]
  change nativeField (Finsupp.single 0 (currentPolynomial (p48qAction (Pi.single i 1)))) = _
  rw [← currentAlong_eq_polynomial, nativeField_current, currentField_action]

#print axioms nativeField_current

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeMonodromy
