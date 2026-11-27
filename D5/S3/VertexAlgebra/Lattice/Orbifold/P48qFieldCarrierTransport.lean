import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeResidueIterate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalZero
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFullEnergySpectrum

/-! Transport of the cubic twisted field comparison along a complex linear equivalence. -/

set_option autoImplicit false

open scoped BigOperators VertexOperator

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFieldCarrierTransport

open SignedFieldResidueLocality (residueField residueCoefficient residueLeft residueRight)
open P48qAllJetWickField (NativeStates nativeField)
open P48qThirdTwistedField (Cartan State)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open P48qNativeCurrentLocality (InResidue currentAlong)
open P48qNativeResidueIterate (TwistedBorcherdsAt targetField_eq_nativeField_of_generators
  targetField_eq_nativeField_of_twisted_borcherds)
open NativeStandardThirdLift (standardLift)
open LatticeAllStateReconstruction (mu)

variable {Γ : Type*} [PartialOrder Γ]
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Pull a Hahn field on `W` back to `V` by conjugating each coefficient. -/
def pullbackField (e : V ≃ₗ[ℂ] W) :
    HVertexOperator Γ ℂ W W →ₗ[ℂ] HVertexOperator Γ ℂ V V where
  toFun A := HVertexOperator.of_coeff (fun k => e.symm.conj (HVertexOperator.coeff A k)) (by
    intro v
    have hs : (Function.support fun k => e.symm.conj (HVertexOperator.coeff A k) v) =
        Function.support (fun k => HVertexOperator.coeff A k (e v)) := by
      ext k
      simp [LinearEquiv.conj_apply_apply]
    rw [hs]
    exact A.isPWO_support_coeff (e v))
  map_add' A B := by
    apply HVertexOperator.coeff_inj
    funext k
    simp only [HVertexOperator.coeff_of_coeff, map_add, Pi.add_apply]
  map_smul' c A := by
    apply HVertexOperator.coeff_inj
    funext k
    simp only [RingHom.id_apply, HVertexOperator.coeff_of_coeff, map_smul, Pi.smul_apply]

theorem pullbackField_coeff (e : V ≃ₗ[ℂ] W) (A : HVertexOperator Γ ℂ W W) (k : Γ) :
    HVertexOperator.coeff (pullbackField e A) k = e.symm.conj (HVertexOperator.coeff A k) := rfl

private theorem pullbackField_ncoeff (e : V ≃ₗ[ℂ] W) (A : VertexOperator ℂ W) (k : ℤ) :
    (pullbackField e A)[[k]] = e.symm.conj (A[[k]]) := rfl

private theorem pullbackField_symm (e : V ≃ₗ[ℂ] W) (A : HVertexOperator Γ ℂ V V) :
    pullbackField e (pullbackField e.symm A) = A := by
  apply HVertexOperator.coeff_inj
  funext k
  apply LinearMap.ext
  intro v
  simp only [pullbackField_coeff, LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
    LinearEquiv.symm_apply_apply]

/-- Conjugation commutes with signed residues, using both vectorwise finite sums. -/
theorem residueCoefficient_pullback (e : V ≃ₗ[ℂ] W) (c : ℂ) (r n : ℤ)
    (A B : VertexOperator ℂ W) (v : V) :
    residueCoefficient c r n (pullbackField e A) (pullbackField e B) v =
      e.symm (residueCoefficient c r n A B (e v)) := by
  have hleft : residueLeft r n (pullbackField e A) (pullbackField e B) v =
      e.symm (residueLeft r n A B (e v)) := by
    unfold residueLeft
    rw [map_finsum e.symm ((residueField c r A B).left_finite n (e v))]
    apply finsum_congr
    intro j
    simp only [pullbackField_ncoeff, LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
      LinearEquiv.apply_symm_apply, map_smul]
  have hright : residueRight r n (pullbackField e A) (pullbackField e B) v =
      e.symm (residueRight r n A B (e v)) := by
    unfold residueRight
    rw [map_finsum e.symm ((residueField c r A B).right_finite n (e v))]
    apply finsum_congr
    intro j
    simp only [pullbackField_ncoeff, LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
      LinearEquiv.apply_symm_apply, map_smul]
  simp only [residueCoefficient, hleft, hright, map_sub, map_smul]

private theorem residueField_ncoeff_pullback (e : V ≃ₗ[ℂ] W) (c : ℂ) (r n : ℤ)
    (A B : VertexOperator ℂ W) :
    ((residueField c r (pullbackField e A) (pullbackField e B)).operator)[[n]] =
      e.symm.conj (((residueField c r A B).operator)[[n]]) := by
  apply LinearMap.ext
  intro v
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, (residueField c r A B).coefficient,
    (residueField c r (pullbackField e A) (pullbackField e B)).coefficient]
  exact residueCoefficient_pullback e c r n A B v

/-- The Laurent exponents of the field on `W` are supported in the class `s` modulo three. -/
def InResidueOn (s : ℤ) (A : VertexOperator ℂ W) : Prop :=
  ∀ k : ℤ, k % 3 ≠ s % 3 → HVertexOperator.coeff A k = 0

/-- Pullback preserves and reflects the exact residue support condition. -/
theorem inResidueOn_pullback_iff (e : V ≃ₗ[ℂ] W) (s : ℤ) (A : VertexOperator ℂ W) :
    InResidueOn s (pullbackField e A) ↔ InResidueOn s A := by
  simp only [InResidueOn, pullbackField_coeff]
  constructor
  · intro h k hk
    exact e.symm.conj.injective ((h k hk).trans (map_zero e.symm.conj).symm)
  · intro h k hk
    rw [h k hk, map_zero]

/-- Read the class `s` in the integral coordinate by taking the coefficients `3k + s`. -/
def stripResidueOn (s : ℤ) (A : VertexOperator ℂ W) : VertexOperator ℂ W :=
  VertexOperator.of_coeff (fun k => HVertexOperator.coeff A (3 * k + s)) (by
    intro w
    refine ⟨min 0 (((HahnModule.of ℂ).symm (A w)).order - s), ?_⟩
    intro k hk
    by_contra! h
    exact hk (VertexOperator.coeff_eq_zero_of_lt_order A _ w (by omega)))

private theorem stripResidueOn_pullback (e : V ≃ₗ[ℂ] W) (s : ℤ) (A : VertexOperator ℂ W) :
    stripResidueOn s (pullbackField e A) = pullbackField e (stripResidueOn s A) := by
  apply HVertexOperator.coeff_inj
  rfl

/-- The cubic twisted Borcherds identity on `W`, with fractional modes `p - s/3`
and `q - t/3` and with the finite sum indexed by the source cutoff `N`. -/
def TwistedBorcherdsOn (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W) (a b : NativeStates)
    (s t : ℤ) (N : ℕ) : Prop :=
  ∀ p q n : ℤ,
    ((residueField 1 n
      (stripResidueOn (s - 3 * p) (Y a)) (stripResidueOn t (Y b))).operator)[[q]] =
      ∑ j ∈ Finset.range ((N : ℤ) - n).toNat,
        Ring.choose ((p : ℂ) - (s : ℂ) / 3) j •
          HVertexOperator.coeff (Y (mu lattice a (n + (j : ℤ)) b))
            (s + t - 3 * (p + q - (j : ℤ) + 1))

/-- The same cubic identity, with the same cutoff, holds before and after pullback. -/
theorem twistedBorcherdsOn_pullback_iff (e : V ≃ₗ[ℂ] W)
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W) (a b : NativeStates) (s t : ℤ) (N : ℕ) :
    TwistedBorcherdsOn ((pullbackField e).comp Y) a b s t N ↔
      TwistedBorcherdsOn Y a b s t N := by
  have mode (p q n : ℤ) :
      ((residueField 1 n (stripResidueOn (s - 3 * p) (pullbackField e (Y a)))
        (stripResidueOn t (pullbackField e (Y b)))).operator)[[q]] =
          e.symm.conj (((residueField 1 n (stripResidueOn (s - 3 * p) (Y a))
            (stripResidueOn t (Y b))).operator)[[q]]) := by
    rw [stripResidueOn_pullback, stripResidueOn_pullback, residueField_ncoeff_pullback]
  simp only [TwistedBorcherdsOn, LinearMap.comp_apply, mode, pullbackField_coeff,
    ← map_smul, ← map_sum, EmbeddingLike.apply_eq_iff_eq]

local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

/-- Actual agreement on charge grounds and lift eigen-currents determines every
target field. The cubic identity is required for an eigen-current in the first
slot, with a cutoff that annihilates the corresponding source products. -/
theorem targetField_eq_transport_of_generators (e : State ≃ₗ[ℂ] W)
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
    (hground : ∀ a : LatticeGeneratingFieldLocality.Charge lattice,
      Y (Finsupp.single a 1) = pullbackField e.symm (nativeField (Finsupp.single a 1)))
    (hcurrent : ∀ (u : Cartan) (s : ℤ),
      σ (currentAlong lattice u) = ζ ^ s • currentAlong lattice u →
      Y (currentAlong lattice u) = pullbackField e.symm (nativeField (currentAlong lattice u)))
    (hresidue : ∀ (v : NativeStates) (t : ℤ), σ v = ζ ^ t • v → InResidueOn t (Y v))
    (hborcherds : ∀ (u : Cartan) (v : NativeStates) (s t : ℤ),
      σ (currentAlong lattice u) = ζ ^ s • currentAlong lattice u → σ v = ζ ^ t • v →
      ∃ N : ℕ, (∀ n ≥ (N : ℤ), mu lattice (currentAlong lattice u) n v = 0) ∧
        TwistedBorcherdsOn Y (currentAlong lattice u) v s t N) :
    Y = (pullbackField e.symm).comp nativeField := by
  have h : (pullbackField e).comp Y = nativeField := by
    apply targetField_eq_nativeField_of_generators
    · intro a
      rw [LinearMap.comp_apply, hground a, pullbackField_symm]
    · intro u s hu
      rw [LinearMap.comp_apply, hcurrent u s hu, pullbackField_symm]
    · intro v t hv
      show InResidue t (pullbackField e (Y v))
      exact (inResidueOn_pullback_iff e t (Y v)).mpr (hresidue v t hv)
    · intro u v s t hu hv
      obtain ⟨N, hcut, hN⟩ := hborcherds u v s t hu hv
      refine ⟨N, hcut, ?_⟩
      show TwistedBorcherdsAt ((pullbackField e).comp Y) (currentAlong lattice u) v s t N
      exact (twistedBorcherdsOn_pullback_iff e Y _ v s t N).mpr hN
  apply LinearMap.ext
  intro v
  have hv := DFunLike.congr_fun h v
  change pullbackField e (Y v) = nativeField v at hv
  rw [LinearMap.comp_apply, ← hv]
  simpa only [LinearEquiv.symm_symm] using (pullbackField_symm e.symm (Y v)).symm

open HalfFockSpectralFiberSource (actualInverse)
open LatticeActualConformalState (omega)
open P48qChargedResidueProduct (mu_eigen)
open P48qConformalVectorDecomposition (currentPair omega_decomposition)
open P48qMomentumEnergy (Fixed fixedBasis fixedGramDual)
open ThirdEigenspacePairing (p48qAction p48qBasis p48qOppositeBasis)
open private lift_current currentStateLinear from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality
open private mem_fixed_iff from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMomentumEnergy

/-- The conformal field is determined by agreement on lift eigen-currents,
residue support, and the cubic identity for pairs of lift eigen-currents. -/
theorem targetConformalField_eq_transport_of_currents (e : State ≃ₗ[ℂ] W)
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
    (hcurrent : ∀ (u : Cartan) (s : ℤ),
      σ (currentAlong lattice u) = ζ ^ s • currentAlong lattice u →
      Y (currentAlong lattice u) = pullbackField e.symm (nativeField (currentAlong lattice u)))
    (hresidue : ∀ (v : NativeStates) (t : ℤ), σ v = ζ ^ t • v → InResidueOn t (Y v))
    (hborcherds : ∀ (u v : Cartan) (s t : ℤ),
      σ (currentAlong lattice u) = ζ ^ s • currentAlong lattice u →
      σ (currentAlong lattice v) = ζ ^ t • currentAlong lattice v →
      ∃ N : ℕ, (∀ n ≥ (N : ℤ), mu lattice (currentAlong lattice u) n (currentAlong lattice v) = 0) ∧
        TwistedBorcherdsOn Y (currentAlong lattice u) (currentAlong lattice v) s t N) :
    Y (omega lattice (actualInverse lattice)) =
      pullbackField e.symm (nativeField (omega lattice (actualInverse lattice))) := by
  have hpair (u v : Cartan) (s t : ℤ)
      (hu : σ (currentAlong lattice u) = ζ ^ s • currentAlong lattice u)
      (hv : σ (currentAlong lattice v) = ζ ^ t • currentAlong lattice v) :
      Y (currentPair u v) = pullbackField e.symm (nativeField (currentPair u v)) := by
    let a := currentAlong lattice u
    let b := currentAlong lattice v
    obtain ⟨N, hcut, hN⟩ := hborcherds u v s t hu hv
    have hagree : pullbackField e (Y (currentPair u v)) = nativeField (currentPair u v) := by
      exact targetField_eq_nativeField_of_twisted_borcherds ((pullbackField e).comp Y) a b s t
        hu hv
        (by rw [LinearMap.comp_apply, hcurrent u s hu, pullbackField_symm])
        (by rw [LinearMap.comp_apply, hcurrent v t hv, pullbackField_symm])
        (fun n => (inResidueOn_pullback_iff e (s + t) (Y (mu lattice a n b))).mpr
          (hresidue _ (s + t) (mu_eigen a b s t n hu hv)))
        ⟨N, hcut, (twistedBorcherdsOn_pullback_iff e Y a b s t N).mpr hN⟩ (-1)
    rw [← hagree]
    simpa only [LinearEquiv.symm_symm] using (pullbackField_symm e.symm (Y (currentPair u v))).symm
  have hlift (u : Cartan) (s : ℤ) (hu : p48qAction u = ζ ^ s • u) :
      σ (currentAlong lattice u) = ζ ^ s • currentAlong lattice u := by
    rw [lift_current u, hu]
    exact currentStateLinear.map_smul _ _
  have hfixed (u : Fixed) : σ (currentAlong lattice u) = ζ ^ (0 : ℤ) • currentAlong lattice u :=
    hlift u 0 (by simpa only [zpow_zero, one_smul] using (mem_fixed_iff u).mp u.property)
  have hζ : IsPrimitiveRoot ζ 3 :=
    IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive
  have hfixedPair (i : Fin 16) :
      Y (currentPair (fixedBasis i) (fixedGramDual fixedBasis i)) =
        pullbackField e.symm (nativeField (currentPair (fixedBasis i) (fixedGramDual fixedBasis i))) :=
    hpair _ _ 0 0 (hfixed _) (hfixed _)
  have hmovingPair (i : Fin 16) :
      Y (currentPair (p48qBasis hζ i) (p48qOppositeBasis hζ i)) =
        pullbackField e.symm (nativeField (currentPair (p48qBasis hζ i) (p48qOppositeBasis hζ i))) :=
    hpair _ _ 1 2
      (hlift _ 1 (by simpa only [zpow_one] using
        Module.End.mem_eigenspace_iff.mp (p48qBasis hζ i).property))
      (hlift _ 2 (by
        rw [show ζ ^ (2 : ℤ) = ζ ^ (2 : ℕ) from zpow_natCast ζ 2]
        exact Module.End.mem_eigenspace_iff.mp (p48qOppositeBasis hζ i).property))
  rw [omega_decomposition hζ]
  simp only [map_add, map_smul, map_sum, hfixedPair, hmovingPair]

open P48qNativeConformalZero (native_conformal_coeff_neg_six_eq_totalLZero)
open P48qTwistedStateEnergy (totalLZero totalLZero_no_integer_eigenvalue)
open P48qFullEnergySpectrum (totalLZero_exact_eigenvalues)

private theorem targetConformalMode_eq_conj_of_field_eq (e : State ≃ₗ[ℂ] W)
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
    (hY : Y (omega lattice (actualInverse lattice)) =
      pullbackField e.symm (nativeField (omega lattice (actualInverse lattice)))) :
    HVertexOperator.coeff (Y (omega lattice (actualInverse lattice))) (-6) = e.conj totalLZero := by
  rw [hY, pullbackField_coeff, native_conformal_coeff_neg_six_eq_totalLZero, LinearEquiv.symm_symm]

/-- Agreement at the conformal vector excludes every integer eigenvalue. -/
theorem targetConformalMode_ne_integer_of_field_eq (e : State ≃ₗ[ℂ] W)
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
    (hY : Y (omega lattice (actualInverse lattice)) =
      pullbackField e.symm (nativeField (omega lattice (actualInverse lattice))))
    (m : ℤ) (w : W) (hw : w ≠ 0) :
    HVertexOperator.coeff (Y (omega lattice (actualInverse lattice))) (-6) w ≠
      (m : ℂ) • w := by
  intro h
  rw [targetConformalMode_eq_conj_of_field_eq e Y hY, LinearEquiv.conj_apply_apply] at h
  exact totalLZero_no_integer_eigenvalue m (e.symm w) (by simpa using hw)
    (by simpa only [LinearEquiv.symm_apply_apply, map_smul] using congrArg e.symm h)

/-- The transported actual conformal zero mode has no integer eigenvalue. -/
theorem targetConformalMode_ne_integer_of_comparison (e : State ≃ₗ[ℂ] W)
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
    (hY : Y = (pullbackField e.symm).comp nativeField)
    (m : ℤ) (w : W) (hw : w ≠ 0) :
    HVertexOperator.coeff (Y (omega lattice (actualInverse lattice))) (-6) w ≠
      (m : ℂ) • w :=
  targetConformalMode_ne_integer_of_field_eq e Y
    (DFunLike.congr_fun hY (omega lattice (actualInverse lattice))) m w hw

/-- Agreement at the conformal vector transports the exact complex point spectrum. -/
theorem targetConformalMode_exact_eigenvalues_of_field_eq (e : State ≃ₗ[ℂ] W)
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
    (hY : Y (omega lattice (actualInverse lattice)) =
      pullbackField e.symm (nativeField (omega lattice (actualInverse lattice)))) (a : ℂ) :
    (∃ w : W, w ≠ 0 ∧ HVertexOperator.coeff (Y (omega lattice (actualInverse lattice))) (-6) w =
      a • w) ↔ ∃ n : ℕ, a = 16 / 9 + (n : ℂ) / 3 := by
  rw [targetConformalMode_eq_conj_of_field_eq e Y hY, ← totalLZero_exact_eigenvalues]
  constructor
  · rintro ⟨w, hw, heigen⟩
    refine ⟨e.symm w, by simpa using hw, ?_⟩
    rw [LinearEquiv.conj_apply_apply] at heigen
    simpa only [LinearEquiv.symm_apply_apply, map_smul] using congrArg e.symm heigen
  · rintro ⟨v, hv, heigen⟩
    refine ⟨e v, by simpa using hv, ?_⟩
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, heigen, map_smul]

run_cmd do
  for name in [``pullbackField, ``pullbackField_coeff, ``residueCoefficient_pullback,
      ``inResidueOn_pullback_iff, ``twistedBorcherdsOn_pullback_iff,
      ``targetField_eq_transport_of_generators, ``targetConformalField_eq_transport_of_currents,
      ``targetConformalMode_ne_integer_of_field_eq, ``targetConformalMode_ne_integer_of_comparison,
      ``targetConformalMode_exact_eigenvalues_of_field_eq] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
      throwError "Unexpected axiom closure for {name}: {axioms}"
    Lean.logInfo m!"{name} depends on axioms: {axioms}"

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFieldCarrierTransport
