/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativePairwiseLocality
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pairwise cover locality on the full native twisted state field. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentLocality
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedLocality

/-! Physical pairwise locality of the complete native P48q twisted state field. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality

open LatticeGeneratingFieldLocality (Charge)
open LatticeAllStateField (Y)
open LatticeAllStateReconstruction (mu)
open NativeStandardThirdLift (standardLift standardLift_single standardLift_ground_single
  standardLift_compatible standardLift_cube)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open P48qThirdTwistedField (Cartan concreteChargedField chargedField fieldCoeff fixedDualBases
  chargedLocalityOrder chargedLocalityPolynomial fieldCoeff_pairwise_locality)
open P48qAllJetWickField (NativeStates NativeIndex NativePolynomial nativeField nativeField_ground
  oscillatorOccurrences nativeWordPolynomial)
open P48qNativeCurrentLocality (Field CoverLocal coverDelta coverComm native_current_local
  native_negativeCurrent_local)
open P48qTwistedHeisenberg (project project_action)
open ThirdTwistedIterate (currentAlong)
open ThirdEigenspacePairing (p48qAction)
open LatticeActualConformalState (currentState)

open private Distribution coverLocal_iff localCoefficients from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentLocality
open private currentPolynomial currentAlong_eq_polynomial from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField
open private oscillator_X_eq_jetPolynomial jetPolynomial from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeMonodromy
open private nativeWordPolynomial_eq_monomial from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qAllJetWickField
open private mu_current_negative_single from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeNegativeCurrentIterate

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "σ" => standardLift lattice g g_cube g_isometry

private def localStates (v : NativeStates) : Submodule ℂ NativeStates :=
  (localCoefficients (nativeField v)).comap (HVertexOperator.coeff.comp nativeField)

private theorem mem_localStates (u v : NativeStates) :
    u ∈ localStates v ↔ CoverLocal (nativeField u) (nativeField v) :=
  (coverLocal_iff _ _).symm

private theorem coverDelta_swap (A B : Field) (N : ℕ) (k l : ℤ) :
    coverDelta^[N] (coverComm B A) k l =
      (-1 : ℂ) ^ N • -(coverDelta^[N] (coverComm A B) l k) := by
  induction N generalizing k l with
  | zero => simp [coverComm, LieRing.of_associative_ring_bracket, neg_sub]
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', coverDelta, coverDelta,
      ih, ih, pow_succ]
    simp only [mul_neg, mul_one, neg_smul, smul_neg, smul_sub]
    abel

private theorem coverLocal_symm {A B : Field} (h : CoverLocal A B) : CoverLocal B A := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  funext k l
  rw [coverDelta_swap, hN]
  simp

/-- A finite cover polynomial acts by translating the two Laurent indices. -/
private def polynomialShift (F : Distribution) :
    MvPolynomial (Fin 2) ℂ →ₗ[ℂ] Distribution :=
  (MvPolynomial.basisMonomials (Fin 2) ℂ).constr ℂ
    (fun e k l => F (k - (e 0 : ℤ)) (l - (e 1 : ℤ)))

private theorem polynomialShift_monomial (F : Distribution) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    polynomialShift F (MvPolynomial.monomial e c) =
      fun k l => c • F (k - (e 0 : ℤ)) (l - (e 1 : ℤ)) := by
  have he : MvPolynomial.monomial e c = c • MvPolynomial.monomial e 1 := by
    rw [← (MvPolynomial.monomial e).map_smul, smul_eq_mul, mul_one]
  rw [he, map_smul, polynomialShift]
  have h := (MvPolynomial.basisMonomials (Fin 2) ℂ).constr_basis ℂ
    (fun e k l => F (k - (e 0 : ℤ)) (l - (e 1 : ℤ))) e
  rw [show MvPolynomial.monomial e (1 : ℂ) = MvPolynomial.basisMonomials (Fin 2) ℂ e by rfl, h]
  rfl

private theorem polynomialShift_mul_cube (F : Distribution) (j : Fin 2)
    (Q : MvPolynomial (Fin 2) ℂ) :
    polynomialShift F (MvPolynomial.X j ^ 3 * Q) = fun k l =>
      polynomialShift F Q (k - ((Finsupp.single j (3 : ℕ)) 0 : ℤ))
        (l - ((Finsupp.single j (3 : ℕ)) 1 : ℤ)) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, one_mul,
      polynomialShift_monomial, polynomialShift_monomial]
    funext k l
    simp only [Finsupp.add_apply, Nat.cast_add]
    rw [sub_sub, sub_sub]
  | add P Q hP hQ =>
    rw [mul_add, map_add, hP, hQ, map_add]
    rfl

private theorem polynomialShift_locality (F : Distribution) (N : ℕ) :
    polynomialShift F (chargedLocalityPolynomial N) = coverDelta^[N] F := by
  induction N with
  | zero =>
    rw [chargedLocalityPolynomial, pow_zero,
      show (1 : MvPolynomial (Fin 2) ℂ) = MvPolynomial.monomial 0 1 by simp,
      polynomialShift_monomial, Function.iterate_zero_apply]
    simp only [Finsupp.zero_apply, Nat.cast_zero, sub_zero, one_smul]
  | succ N ih =>
    rw [chargedLocalityPolynomial, pow_succ', sub_mul, map_sub, polynomialShift_mul_cube,
      polynomialShift_mul_cube, ← chargedLocalityPolynomial, ih, Function.iterate_succ_apply']
    funext k l
    norm_num [coverDelta, Finsupp.single_apply]

private abbrev chargeGround (a : Charge lattice) : NativeStates := Finsupp.single a 1

private theorem ground_local (a b : Charge lattice) :
    CoverLocal (nativeField (chargeGround a)) (nativeField (chargeGround b)) := by
  rw [nativeField_ground, nativeField_ground]
  let N := chargedLocalityOrder a b
  let Q := chargedLocalityPolynomial N
  refine ⟨N, ?_⟩
  rw [← polynomialShift_locality]
  change polynomialShift (coverComm (concreteChargedField a) (concreteChargedField b)) Q = 0
  rw [Q.as_sum, map_sum]
  funext k l
  simp only [Finset.sum_apply, polynomialShift_monomial, coverComm,
    LieRing.of_associative_ring_bracket]
  exact fieldCoeff_pairwise_locality fixedDualBases a b k l

private theorem zeta_primitive : IsPrimitiveRoot ζ 3 :=
  IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive

private theorem root_cube (r : ℕ) : (ζ ^ r) ^ 3 = 1 := by
  rw [pow_right_comm, zeta_primitive.pow_eq_one, one_pow]

private theorem fourier_sum {V : Type*} [AddCommGroup V] [Module ℂ V] (a b c : V) :
    (∑ r : Fin 3, (3 : ℂ)⁻¹ • (a + ζ ^ r.val • b + (ζ ^ r.val) ^ 2 • c)) = a := by
  have hζ : 1 + ζ + ζ ^ 2 = 0 := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] using
      zeta_primitive.geom_sum_eq_zero (by decide : 1 < 3)
  have hζ4 : (ζ ^ 2) ^ 2 = ζ := by
    calc
      (ζ ^ 2) ^ 2 = ζ ^ 3 * ζ := by ring
      _ = ζ := by rw [zeta_primitive.pow_eq_one, one_mul]
  rw [← Finset.smul_sum]
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
    one_pow, hζ4]
  calc
    _ = (3 : ℂ)⁻¹ • ((3 : ℂ) • a + (1 + ζ + ζ ^ 2) • b + (1 + ζ + ζ ^ 2) • c) := by module
    _ = a := by
      simp only [hζ, zero_smul, add_zero, smul_smul,
        inv_mul_cancel₀ (by norm_num : (3 : ℂ) ≠ 0), one_smul]

private def liftProject (r : Fin 3) (v : NativeStates) : NativeStates :=
  (3 : ℂ)⁻¹ • (v + ζ ^ r.val • σ v + (ζ ^ r.val) ^ 2 • σ (σ v))

private theorem liftProject_eigen (r : Fin 3) (v : NativeStates) :
    σ (liftProject r v) = (ζ ^ r.val) ^ 2 • liftProject r v := by
  let z := ζ ^ r.val
  have hz : z ^ 3 = 1 := root_cube _
  have h₁ : z ^ 2 * z = 1 := by rw [← pow_succ, hz]
  have h₂ : z ^ 2 * z ^ 2 = z := by
    rw [← pow_add, show 2 + 2 = 3 + 1 by decide, pow_add, hz, pow_one, one_mul]
  have hσ : σ (σ (σ v)) = v := by
    have h := DFunLike.congr_fun (standardLift_cube lattice g g_cube g_isometry) v
    change (σ ^ 3) v = v at h
    simpa only [pow_succ', pow_zero, mul_one, LinearEquiv.mul_apply]
      using h
  change σ ((3 : ℂ)⁻¹ • (v + z • σ v + z ^ 2 • σ (σ v))) = _
  unfold liftProject
  change _ = z ^ 2 • ((3 : ℂ)⁻¹ • (v + z • σ v + z ^ 2 • σ (σ v)))
  rw [map_smul, smul_comm (z ^ 2) ((3 : ℂ)⁻¹)]
  apply congrArg (fun w : NativeStates => (3 : ℂ)⁻¹ • w)
  simp only [map_add, map_smul, hσ, smul_add, smul_smul, h₁, h₂, one_smul]
  abel

private def groundSpan : Submodule ℂ NativeStates :=
  Submodule.span ℂ (Set.range chargeGround)

private theorem lift_groundSpan {v : NativeStates} (hv : v ∈ groundSpan) :
    σ v ∈ groundSpan := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, rfl⟩ := hv
    rw [chargeGround, standardLift_ground_single]
    exact groundSpan.smul_mem _ (Submodule.subset_span ⟨g a, rfl⟩)
  | zero => simp [map_zero]
  | add v w _ _ hv hw => rw [map_add]; exact groundSpan.add_mem hv hw
  | smul c v _ hv => rw [map_smul]; exact groundSpan.smul_mem c hv

private theorem groundProject_mem (a : Charge lattice) (r : Fin 3) :
    liftProject r (chargeGround a) ∈ groundSpan := by
  have h : chargeGround a ∈ groundSpan := Submodule.subset_span ⟨a, rfl⟩
  exact groundSpan.smul_mem _ (groundSpan.add_mem
    (groundSpan.add_mem h (groundSpan.smul_mem _ (lift_groundSpan h)))
    (groundSpan.smul_mem _ (lift_groundSpan (lift_groundSpan h))))

private theorem local_on_span {S : Set NativeStates}
    (h : ∀ u ∈ S, ∀ v ∈ S, CoverLocal (nativeField u) (nativeField v))
    {u v : NativeStates} (hu : u ∈ Submodule.span ℂ S) (hv : v ∈ Submodule.span ℂ S) :
    CoverLocal (nativeField u) (nativeField v) := by
  have left {w : NativeStates} (hw : ∀ x ∈ S, CoverLocal (nativeField x) (nativeField w)) :
      Submodule.span ℂ S ≤ localStates w :=
    Submodule.span_le.mpr fun x hx => (mem_localStates x w).mpr (hw x hx)
  apply (mem_localStates u v).mp (left (fun x hx => coverLocal_symm
    ((mem_localStates v x).mp (left (fun y hy => h y hy x hx) hv))) hu)

private def currentStateLinear : Cartan →ₗ[ℂ] NativeStates where
  toFun := currentAlong lattice
  map_add' u v := by
    change (∑ i : Fin 48, (u i + v i) • currentState lattice i) =
      (∑ i : Fin 48, u i • currentState lattice i) +
        ∑ i : Fin 48, v i • currentState lattice i
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' c u := by
    change (∑ i : Fin 48, (c * u i) • LatticeActualConformalState.currentState lattice i) =
      c • ∑ i : Fin 48, u i • LatticeActualConformalState.currentState lattice i
    simp only [Finset.smul_sum, smul_smul]

private theorem lift_current (u : Cartan) :
    σ (currentAlong lattice u) = currentAlong lattice (p48qAction u) := by
  have h0 : g (0 : Charge lattice) = 0 := map_zero g
  have hη := ThirdTwistedChargeAction.nativeStandardEta_fixed lattice g g_isometry 0 h0
  simp only [currentAlong_eq_polynomial, standardLift_single, h0, hη, Units.val_one, one_smul]
  congr 1
  simp only [currentPolynomial, map_sum, map_smul]
  have hX (i : Fin lattice.rank) :
      IsometryLift.oscillator lattice g (MvPolynomial.X (i, 0)) =
        ∑ j : Fin lattice.rank, p48qAction (Pi.single i 1) j •
          (MvPolynomial.X (j, 0) : NativePolynomial) := by
    simpa [P48qAllJetWickField.oscillatorJet, jetPolynomial] using
      oscillator_X_eq_jetPolynomial (i, 0)
  simp_rw [hX, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hu : (∑ i : Fin 48, u i • Pi.single i (1 : ℂ)) = u := by
    classical
    ext i
    simp [Pi.single_apply]
  have hj : (∑ i : Fin 48, u i * p48qAction (Pi.single i 1) j) = p48qAction u j := by
    conv_rhs => rw [← hu]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ i : Fin 48, u i • (p48qAction (Pi.single i 1) j •
    (MvPolynomial.X (j, 0) : NativePolynomial))) = _
  simp_rw [smul_smul]
  rw [← Finset.sum_smul, hj]

private abbrev prepend (d : ℕ+) (u : Cartan) (v : NativeStates) : NativeStates :=
  mu lattice (currentAlong lattice u) (-((d : ℕ) : ℤ)) v

private theorem prepend_eigen (d : ℕ+) (u : Cartan) (r : Fin 3) (v : NativeStates) (s : ℤ)
    (hu : p48qAction u = (ζ ^ r.val) ^ 2 • u) (hv : σ v = ζ ^ s • v) :
    σ (prepend d u v) = ζ ^ (((r.val * 2 : ℕ) : ℤ) + s) • prepend d u v := by
  have hcurrent : σ (currentAlong lattice u) = (ζ ^ r.val) ^ 2 • currentAlong lattice u := by
    rw [lift_current, hu]
    exact currentStateLinear.map_smul _ _
  unfold prepend mu
  rw [(standardLift_compatible lattice g g_cube g_isometry).2.1, hcurrent, hv]
  simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, smul_smul]
  rw [← pow_mul, ← zpow_natCast, ← zpow_add₀ (Units.ne_zero ThirdTwistedChargeCocycle.zeta)]
  rw [add_comm s]

private inductive EigenWord : ℕ → NativeStates → Prop
  | ground (a : Charge lattice) (r : Fin 3) : EigenWord 0 (liftProject r (chargeGround a))
  | cons {n : ℕ} {v : NativeStates} (tail : EigenWord n v)
      (d : ℕ+) (u : Cartan) (r : Fin 3) (hu : p48qAction u = (ζ ^ r.val) ^ 2 • u) :
      EigenWord (n + 1) (prepend d u v)

private theorem EigenWord.eigen {n : ℕ} {v : NativeStates} (h : EigenWord n v) :
    ∃ s : ℤ, σ v = ζ ^ s • v := by
  induction h with
  | ground a r =>
    refine ⟨((r.val * 2 : ℕ) : ℤ), ?_⟩
    simpa only [zpow_natCast, pow_mul] using liftProject_eigen r (chargeGround a)
  | cons tail d u r hu ih =>
    obtain ⟨s, hs⟩ := ih
    exact ⟨_, prepend_eigen d u r _ s hu hs⟩

private theorem eigenWord_local {i j : ℕ} {v w : NativeStates}
    (hv : EigenWord i v) (hw : EigenWord j w) :
    CoverLocal (nativeField v) (nativeField w) := by
  suffices ∀ n : ℕ, ∀ (i j : ℕ) (v w : NativeStates), i + j = n →
      EigenWord i v → EigenWord j w → CoverLocal (nativeField v) (nativeField w) by
    exact this (i + j) i j v w rfl hv hw
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i j v w hlen hv hw
    cases hv with
    | ground a r =>
      cases hw with
      | ground b t =>
        exact local_on_span (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ground_local a b)
          (groundProject_mem a r) (groundProject_mem b t)
      | @cons j w tail d u t hu =>
        obtain ⟨s, hs⟩ := tail.eigen
        exact coverLocal_symm (native_negativeCurrent_local u t.val t.isLt hu d w _ s hs
          (native_current_local u t.val t.isLt hu _)
          (ih (j + 0) (by omega) j 0 w _ rfl tail (.ground a r))
          (native_current_local u t.val t.isLt hu _))
    | @cons i v tail d u r hu =>
      obtain ⟨s, hs⟩ := tail.eigen
      exact native_negativeCurrent_local u r.val r.isLt hu d v w s hs
        (native_current_local u r.val r.isLt hu w)
        (ih (i + j) (by omega) i j v w rfl tail hw)
        (native_current_local u r.val r.isLt hu v)


private def eigenWords : Set NativeStates := { v | ∃ n, EigenWord n v }

private def eigenWordSpan : Submodule ℂ NativeStates := Submodule.span ℂ eigenWords

private theorem eigenWordSpan_prepend_eigen (d : ℕ+) (u : Cartan) (r : Fin 3)
    (hu : p48qAction u = (ζ ^ r.val) ^ 2 • u) {v : NativeStates} (hv : v ∈ eigenWordSpan) :
    prepend d u v ∈ eigenWordSpan := by
  let T := (Y lattice (currentAlong lattice u))[[-((d : ℕ) : ℤ)]]
  change T v ∈ eigenWordSpan
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨n, hn⟩ := hv
    exact Submodule.subset_span ⟨n + 1, hn.cons d u r hu⟩
  | zero => rw [map_zero]; exact eigenWordSpan.zero_mem
  | add v w _ _ hv hw => rw [map_add]; exact eigenWordSpan.add_mem hv hw
  | smul c v _ hv => rw [map_smul]; exact eigenWordSpan.smul_mem c hv

private theorem eigenWordSpan_prepend (d : ℕ+) (u : Cartan) {v : NativeStates}
    (hv : v ∈ eigenWordSpan) : prepend d u v ∈ eigenWordSpan := by
  have hsum : (∑ r : Fin 3, project (ζ ^ r.val) u) = u :=
    fourier_sum u (p48qAction u) (p48qAction (p48qAction u))
  have hmode : prepend d u v = ∑ r : Fin 3, prepend d (project (ζ ^ r.val) u) v := by
    have h := map_sum currentStateLinear (fun r : Fin 3 => project (ζ ^ r.val) u) Finset.univ
    change currentAlong lattice (∑ r : Fin 3, project (ζ ^ r.val) u) =
      ∑ r : Fin 3, currentAlong lattice (project (ζ ^ r.val) u) at h
    rw [hsum] at h
    simp only [prepend, mu, h, map_sum, Finset.sum_apply, LinearMap.sum_apply]
  rw [hmode]
  exact eigenWordSpan.sum_mem fun r _ =>
    eigenWordSpan_prepend_eigen d _ r (project_action _ (root_cube _) u) hv

private theorem eigenWordSpan_ground (a : Charge lattice) : chargeGround a ∈ eigenWordSpan := by
  rw [← fourier_sum (chargeGround a) (σ (chargeGround a)) (σ (σ (chargeGround a)))]
  exact eigenWordSpan.sum_mem fun r _ => Submodule.subset_span ⟨0, EigenWord.ground a r⟩

private theorem eigenWordSpan_word (a : Charge lattice) (word : List NativeIndex) :
    Finsupp.single a (nativeWordPolynomial word) ∈ eigenWordSpan := by
  induction word with
  | nil => exact eigenWordSpan_ground a
  | cons j tail ih =>
    obtain ⟨i, n⟩ := j
    let d : ℕ+ := ⟨n + 1, n.succ_pos⟩
    let u : Cartan := Pi.single i 1
    have h := eigenWordSpan_prepend d u ih
    rw [prepend, mu_current_negative_single] at h
    classical
    simpa [d, u, P48qHigherCurrentIterate.sourceOscillator, Pi.single_apply, nativeWordPolynomial]
      using h

private theorem eigenWordSpan_eq_top : eigenWordSpan = ⊤ := by
  classical
  have single_mem (a : Charge lattice) (P : NativePolynomial) :
      (Finsupp.single a P : NativeStates) ∈ eigenWordSpan := by
    induction P using MvPolynomial.induction_on' with
    | monomial e c =>
      have hword := eigenWordSpan_word a (oscillatorOccurrences e)
      rw [nativeWordPolynomial_eq_monomial,
        show ((oscillatorOccurrences e : List NativeIndex) : Multiset NativeIndex).toFinsupp = e
          by simp [oscillatorOccurrences] ] at hword
      rw [show MvPolynomial.monomial e c = c • MvPolynomial.monomial e 1 by
        rw [← (MvPolynomial.monomial e).map_smul, smul_eq_mul, mul_one],
        ← Finsupp.smul_single]
      exact eigenWordSpan.smul_mem c hword
    | add P Q hP hQ =>
      rw [Finsupp.single_add]
      exact eigenWordSpan.add_mem hP hQ
  apply Submodule.eq_top_iff'.mpr
  intro v
  rw [← Finsupp.sum_single v]
  exact eigenWordSpan.sum_mem fun a _ => single_mem a (v a)

/-- Every pair of actual native P48q twisted fields is local for the physical
difference `x³ - y³`. -/
theorem nativeField_pairwise_locality (v w : NativeStates) :
    CoverLocal (nativeField v) (nativeField w) := by
  have hspan (u : NativeStates) : u ∈ eigenWordSpan := by rw [eigenWordSpan_eq_top]; trivial
  apply local_on_span (S := eigenWords) _ (hspan v) (hspan w)
  rintro u ⟨i, hu⟩ x ⟨j, hx⟩
  exact eigenWord_local hu hx

/--
info:
'D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality.nativeField_pairwise_locality'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms nativeField_pairwise_locality

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality
