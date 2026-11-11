/- GID: D5/S3/VertexAlgebra/Lattice/ActualZhuJointFaithful
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualZhuJointFaithful
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native minimum transition matrix coefficients and joint bottom faithfulness. -/
import D5.S3.VertexAlgebra.Lattice.ActualZhuTransitionSpan
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetZhuRepresentation

/-! The bottom action is the original dual-coset field, with its integral-lattice
epsilon; no cocycle on the dual lattice is introduced.
Dong--Li--Mason, DOI 10.1006/jabr.1997.7112, Theorem 3.4 and Remark 2.11.
The saved native representation attributes the module residue argument to
Fedor K. Popov, Lean_VOA 013a799ca834a8a6b3afa8129e3e522025b3f45c (Apache-2.0). -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.Lattice.ActualZhuJointFaithful
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticePositiveEnergy
open LatticeSugawaraCurrents LatticeAllStateReconstruction
open LatticeDualCosetModule LatticeDualCosetEnergy LatticeDualCosetZhu
open LatticeDiscriminantTheta
open ActualZhuFinite ActualZhuAlgebra ActualZhuGroundCurrent ActualZhuCurrentNormalForm
open ActualZhuMinimum ActualZhuSourceProjectors ActualZhuTransitionSpan
open private creation_zero from D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce
open private charge_pairing from D5.S3.VertexAlgebra.LatticeSugawaraConformal
open scoped BigOperators IsMulCommutative VertexOperator
noncomputable section
variable (D : LatticeData) [hD : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]
local instance : DecidableEq (Transition D hD.out) := Classical.decEq _
local instance : Ring (Q D) := quotientRing D hD.out
local instance : Algebra ℂ (Q D) := quotientAlgebra D hD.out
local instance : IsMulCommutative (currentAlgebra D) :=
  Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _
    exact currents_commute D i j)

abbrev SectorBottom (c : Discriminant D) :=
  Bottom D (dualVector D (representative D c)) hD.out

def rho (c : Discriminant D) : Q D →ₐ[ℂ] Module.End ℂ (SectorBottom D c) :=
  representation D (representative D c) (dualVector D (representative D c))
    (dualVector_hDual D hD.out _) hD.out

def bottomVector (c : Discriminant D) (γ : Min_c D hD.out c) : SectorBottom D c :=
  ⟨carrierBasis D (γ.val,0), by
    change (carrierBasis D).repr (carrierBasis D (γ.val,0)) ∈
      Finsupp.supported ℂ ℂ {a : Label D | weight D (dualVector D (representative D c)) a =
        chargeWeight D (dualVector D (representative D c))
          (minimizingCharge D (dualVector D (representative D c)) hD.out)}
    rw [Module.Basis.repr_self]
    apply Finsupp.single_mem_supported
    simpa [weight, oscillatorEnergy] using γ.property⟩

theorem bottomVector_val (c : Discriminant D) (γ : Min_c D hD.out c) :
    (bottomVector D c γ).val = Finsupp.single γ.val 1 := by
  simp [bottomVector]

theorem current_action (c : Discriminant D) (γ : Min_c D hD.out c) (i : Fin D.rank) :
    rho D c (H D i) (bottomVector D c γ) =
      (minimumWeight D c γ i : ℂ) • bottomVector D c γ := by
  apply Subtype.ext
  rw [rho, H, representation_mk D _ _ _ hD.out 1 _ (current_grade D i)]
  rw [bottomVector_val, LatticeActualConformalState.currentState,
    action_current_coefficients]
  have hb : bilinear D (unitCharge D i) γ.val = (gramMap D γ.val) i := by
    simp [bilinear, unitCharge, gramMap, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  simp [shiftedCurrentPolynomial, hb, minimumWeight, add_comm, ← Finsupp.smul_single,
    bottomVector_val]

private theorem polynomial_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Polynomial ℂ →ₐ[ℂ] Module.End ℂ V) (v : V) (zeta : ℂ)
    (he : f Polynomial.X v = zeta • v) (p : Polynomial ℂ) :
    f p v = p.eval zeta • v := by
  have hf : f = Polynomial.aeval (f Polynomial.X) :=
    Polynomial.algHom_ext (by rw [Polynomial.aeval_X])
  rw [hf]
  exact Module.End.aeval_apply_of_mem_apply_eq_smul he

private def currentRep (c : Discriminant D) :
    currentAlgebra D →ₐ[ℂ] Module.End ℂ (SectorBottom D c) :=
  (rho D c).comp (currentAlgebra D).val

private theorem coordinate_action (c : Discriminant D) (γ : Min_c D hD.out c)
    (i : Fin D.rank) (j : Node D i) :
    currentRep D c (coordinateProjector D i j) (bottomVector D c γ) =
      (if j = minimumGrid D c γ i then (1 : ℂ) else 0) • bottomVector D c γ := by
  classical
  have he := polynomial_action
    ((currentRep D c).comp (Polynomial.aeval (currentGenerator D i)))
    (bottomVector D c γ) (minimumWeight D c γ i : ℂ) (by
      simpa only [AlgHom.comp_apply, Polynomial.aeval_X, currentRep,
        currentGenerator, Subalgebra.val_apply] using current_action D c γ i)
    (Lagrange.basis Finset.univ (fun j : Node D i => (node D i j : ℂ)) j)
  change currentRep D c (coordinateProjector D i j) _ = _ at he
  have hs : (minimumWeight D c γ i : ℂ) =
      (node D i (minimumGrid D c γ i) : ℂ) :=
    congrArg (fun r : Charge D => (r i : ℂ)) (minimumGrid_spec D c γ).symm
  rw [hs] at he
  rw [he]
  have hv : Set.InjOn (fun j : Node D i => (node D i j : ℂ))
      (Finset.univ : Finset (Node D i)) := by
    intro a _ b _ hab
    have hz : node D i a = node D i b := Int.cast_injective hab
    apply Fin.ext
    dsimp [node] at hz
    omega
  by_cases hj : j = minimumGrid D c γ i
  · subst j
    rw [Lagrange.eval_basis_self (v := fun j : Node D i => (node D i j : ℂ)) hv
      (Finset.mem_univ _), ite_eq_left rfl]
  · rw [Lagrange.eval_basis_of_ne (v := fun j : Node D i => (node D i j : ℂ)) hj
      (Finset.mem_univ _), ite_eq_right hj]

theorem projector_action (r : Grid D) (c : Discriminant D) (γ : Min_c D hD.out c) :
    rho D c (projector D r : Q D) (bottomVector D c γ) =
      if r = minimumGrid D c γ then bottomVector D c γ else 0 := by
  classical
  have he (s : Finset (Fin D.rank)) :
      currentRep D c (∏ i ∈ s, coordinateProjector D i (r i)) (bottomVector D c γ) =
      (∏ i ∈ s, if r i = minimumGrid D c γ i then (1 : ℂ) else 0) •
        bottomVector D c γ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, map_mul,
        Module.End.mul_apply, ih, map_smul, coordinate_action, smul_smul, mul_comm]
  change currentRep D c (projector D r) _ = _
  rw [projector, he]
  by_cases hr : r = minimumGrid D c γ
  · subst r
    simp
  · have hn : ∃ i, r i ≠ minimumGrid D c γ i := by
      by_contra hn
      push Not at hn
      exact hr (funext hn)
    obtain ⟨i,hi⟩ := hn
    rw [ite_eq_right hr, Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi), zero_smul]

theorem ground_action (c : Discriminant D) (γout γin : Min_c D hD.out c) :
    rho D c (E D (γout.val - γin.val)) (bottomVector D c γin) =
      epsilon D (γout.val - γin.val) γin.val • bottomVector D c γout := by
  classical
  let δ := γout.val - γin.val
  have ha : γin.val + δ = γout.val := by dsimp [δ]; abel
  have hs : (∑ i, δ i * minimumWeight D c γin i) + chargeEnergy D δ = 0 :=
    (minimum_transition D _ _ (dualVector_hDual D hD.out _) hD.out γin δ).mpr
      (ha.symm ▸ γout.property)
  have hb : bilinear D δ γin.val + (∑ i, δ i * representative D c i) =
      ∑ i, δ i * minimumWeight D c γin i := by
    have hp := charge_pairing D γin.val δ
    have hu (i : Fin D.rank) : bilinear D γin.val (unitCharge D i) =
        gramMap D γin.val i := by
      rw [bilinear_symmetric]
      simp [bilinear, unitCharge, gramMap, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    simp only [hu] at hp
    rw [bilinear_symmetric] at hp
    simp only [minimumWeight, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hp, add_comm]
  have hk : ((chargeEnergy D δ).toNat : ℤ) = chargeEnergy D δ :=
    Int.toNat_of_nonneg (chargeEnergy_nonneg D hD.out δ)
  have hi : -((chargeEnergy D δ).toNat - 1 : ℤ) - 1 - bilinear D δ γin.val -
      (∑ i, δ i * representative D c i) = 0 := by omega
  apply Subtype.ext
  rw [rho, E, representation_mk D _ _ _ hD.out _ _ (ground_grade D δ hD.out),
    bottomVector_val, action_ground_coefficients]
  have ht : translatedPolynomial D δ 1 = Polynomial.C 1 := by
    simp [translatedPolynomial]
  simp only [shiftedRawSingle, ht, Polynomial.support_C one_ne_zero,
    Finset.sum_singleton, Polynomial.coeff_C, one_mul,
    Nat.cast_zero, add_zero]
  rw [hi, creation_zero]
  have ho : δ + γin.val = γout.val := by dsimp [δ]; abel
  simp [ho, δ, bottomVector_val]

private theorem minimumGrid_pair (c d : Discriminant D)
    (γ : Min_c D hD.out c) (η : Min_c D hD.out d)
    (he : minimumGrid D c γ = minimumGrid D d η) :
    (c, γ.val) = (d, η.val) := by
  apply (cosetEquiv D hD.out).injective
  change minimumWeight D c γ = minimumWeight D d η
  rw [← minimumGrid_spec D c γ, ← minimumGrid_spec D d η, he]

private theorem bottomVector_coeff (c : Discriminant D) (γ : Min_c D hD.out c) :
    carrierCoeffEquiv D (bottomVector D c γ).val = Finsupp.single (γ.val,0) 1 := by
  change (carrierBasis D).repr (carrierBasis D (γ.val,0)) = _
  exact (carrierBasis D).repr_self _

private def bottomLabelEquiv (c : Discriminant D) :
    {a : Label D // weight D (dualVector D (representative D c)) a =
      chargeWeight D (dualVector D (representative D c))
        (minimizingCharge D (dualVector D (representative D c)) hD.out)} ≃
      Min_c D hD.out c where
  toFun a := ⟨a.val.1, ((bottom_fiber D _ hD.out a.val).mp a.property).1⟩
  invFun γ := ⟨(γ.val,0), (bottom_fiber D _ hD.out (γ.val,0)).mpr ⟨γ.property,rfl⟩⟩
  left_inv a := by
    apply Subtype.ext
    exact Prod.ext rfl (((bottom_fiber D _ hD.out a.val).mp a.property).2.symm)
  right_inv γ := by apply Subtype.ext; rfl

/-- Transport of the full native grade basis, with all tied minima retained. -/
def bottomBasis (c : Discriminant D) :
    Module.Basis (Min_c D hD.out c) ℂ (SectorBottom D c) :=
  Module.Basis.ofRepr ((gradeCoeffEquiv D (dualVector D (representative D c))
    (chargeWeight D (dualVector D (representative D c))
      (minimizingCharge D (dualVector D (representative D c)) hD.out))).trans
        (Finsupp.domLCongr (bottomLabelEquiv D c)))

set_option maxHeartbeats 1000000 in
-- Dependent transport unfolds the native energy fiber and supported-Finsupp equivalences.
theorem bottomBasis_apply (c : Discriminant D) (γ : Min_c D hD.out c) :
    bottomBasis D c γ = bottomVector D c γ := by
  simp only [bottomBasis, Module.Basis.coe_ofRepr, LinearEquiv.symm_trans_apply,
    Finsupp.domLCongr_symm, Finsupp.domLCongr_single]
  apply Subtype.ext
  apply (carrierCoeffEquiv D).injective
  rw [bottomVector_coeff]
  change carrierCoeffEquiv D ((carrierCoeffEquiv D).symm
    (((Finsupp.supportedEquivFinsupp (R := ℂ) _).symm
      (Finsupp.single ((bottomLabelEquiv D c).symm γ) 1)).val)) = _
  rw [LinearEquiv.apply_symm_apply, Finsupp.supportedEquivFinsupp_symm_single]
  rfl


/-- A coefficient of an actual bottom action, using the original carrier basis. -/
def readout (t : Transition D hD.out) : Q D →ₗ[ℂ] ℂ where
  toFun q := carrierCoeffEquiv D ((rho D t.1 q (bottomBasis D t.1 t.2.2)).val)
    (t.2.1.val, 0)
  map_add' x y := by simp
  map_smul' c x := by simp

theorem transition_matrix_coefficient (t u : Transition D hD.out) :
    readout D t (sourceTransition D u) =
      if u = t then epsilon D (t.2.1.val - t.2.2.val) t.2.2.val else 0 := by
  classical
  change carrierCoeffEquiv D ((rho D t.1 (sourceTransition D u)
    (bottomBasis D t.1 t.2.2)).val) (t.2.1.val,0) = _
  rw [bottomBasis_apply]
  rcases t with ⟨c,γout,γin⟩
  rcases u with ⟨d,ηout,ηin⟩
  by_cases hg : minimumGrid D d ηin = minimumGrid D c γin
  · have hp := minimumGrid_pair D d c ηin γin hg
    have hd : d = c := congrArg Prod.fst hp
    subst d
    have hin : ηin = γin := Subtype.ext (congrArg Prod.snd hp)
    subst ηin
    have he : rho D c (sourceTransition D ⟨c,ηout,γin⟩) (bottomVector D c γin) =
        epsilon D (ηout.val - γin.val) γin.val • bottomVector D c ηout := by
      rw [sourceTransition, map_mul, Module.End.mul_apply, projector_action,
        ite_eq_left rfl, ground_action]
    change carrierCoeffEquiv D ((rho D c _ _).val) (γout.val,0) = _
    rw [he]
    by_cases ho : ηout = γout
    · subst ηout
      simp only [Submodule.coe_smul, map_smul, Finsupp.smul_apply, bottomVector_coeff,
        Finsupp.single_eq_same, smul_eq_mul, mul_one, ite_true]
    · have hv : ηout.val ≠ γout.val := fun h => ho (Subtype.ext h)
      have ht : (⟨c,ηout,γin⟩ : Transition D hD.out) ≠ ⟨c,γout,γin⟩ := by
        intro h
        exact hv (congrArg (fun t : Transition D hD.out => t.2.1.val) h)
      simp [map_smul, bottomVector_coeff, hv, ht, Prod.mk.injEq]
  · have he : rho D c (sourceTransition D ⟨d,ηout,ηin⟩) (bottomVector D c γin) = 0 := by
      rw [sourceTransition, map_mul, Module.End.mul_apply, projector_action,
        ite_eq_right hg, map_zero]
    have ht : (⟨d,ηout,ηin⟩ : Transition D hD.out) ≠ ⟨c,γout,γin⟩ := by
      intro h
      exact hg (congrArg (fun t : Transition D hD.out => minimumGrid D t.1 t.2.2) h)
    change carrierCoeffEquiv D ((rho D c _ _).val) (γout.val,0) = _
    rw [he]
    simp [ht]

omit hD in
private theorem epsilon_nonzero (α β : Charge D) : epsilon D α β ≠ 0 := by
  unfold epsilon paritySign
  split_ifs <;> norm_num

/-- Direct extraction from a finite source combination proves joint faithfulness. -/
theorem joint_kernel_zero (q : Q D) (hq : ∀ c : Discriminant D, rho D c q = 0) : q = 0 := by
  classical
  let : Fintype (Transition D hD.out) := Fintype.ofFinite _
  have hspan : q ∈ Submodule.span ℂ (Set.range (sourceTransition D)) := by
    rw [source_transition_span]
    trivial
  obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hspan
  have hz (t : Transition D hD.out) : a t = 0 := by
    have hr : readout D t q = 0 := by simp [readout, hq]
    rw [← ha, map_sum] at hr
    simp only [map_smul, transition_matrix_coefficient, smul_eq_mul] at hr
    have hs : (∑ u : Transition D hD.out,
        a u * (if u = t then epsilon D (t.2.1.val - t.2.2.val) t.2.2.val else 0)) =
        a t * epsilon D (t.2.1.val - t.2.2.val) t.2.2.val := by simp
    rw [hs] at hr
    exact (mul_eq_zero.mp hr).resolve_right (epsilon_nonzero D _ _)
  rw [← ha]
  simp [hz]

theorem joint_injective : Function.Injective (fun q : Q D =>
    fun c : Discriminant D => rho D c q) := by
  intro x y he
  have hz : x - y = 0 := joint_kernel_zero D (x-y) (fun c => by
    have hc : rho D c x = rho D c y := congrFun he c
    rw [map_sub, hc, sub_self])
  exact sub_eq_zero.mp hz


theorem bottom_dimension (c : Discriminant D) :
    Module.finrank ℂ (SectorBottom D c) = Nat.card (Min_c D hD.out c) := by
  let : Fintype (Min_c D hD.out c) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card] using Module.finrank_eq_card_basis (bottomBasis D c)

theorem transition_linearIndependent : LinearIndependent ℂ (sourceTransition D) := by
  classical
  let : Fintype (Transition D hD.out) := Fintype.ofFinite _
  apply Fintype.linearIndependent_iff.mpr
  intro a ha t
  have hr := congrArg (readout D t) ha
  simp only [map_sum, map_smul, map_zero, transition_matrix_coefficient, smul_eq_mul] at hr
  have hs : (∑ u : Transition D hD.out,
      a u * (if u = t then epsilon D (t.2.1.val - t.2.2.val) t.2.2.val else 0)) =
      a t * epsilon D (t.2.1.val - t.2.2.val) t.2.2.val := by simp
  rw [hs] at hr
  exact (mul_eq_zero.mp hr).resolve_right (epsilon_nonzero D _ _)

def sourceBasis : Module.Basis (Transition D hD.out) ℂ (Q D) :=
  Module.Basis.mk (transition_linearIndependent D) (by rw [source_transition_span])

theorem sharp_card_dimension : Module.finrank ℂ (Q D) = Nat.card (Transition D hD.out) := by
  let : Fintype (Transition D hD.out) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card] using Module.finrank_eq_card_basis (sourceBasis D)

/-- Equality follows from the source basis and actual matrix coefficients; it is
not used to infer the joint injectivity above. -/
theorem sharp_dimension [Fintype (Discriminant D)] :
    Module.finrank ℂ (Q D) =
      ∑ c : Discriminant D, (Module.finrank ℂ (SectorBottom D c))^2 := by
  rw [sharp_card_dimension]
  simp only [Transition, Nat.card_sigma, Nat.card_prod, bottom_dimension, pow_two]

#print axioms projector_action
#print axioms transition_matrix_coefficient
#print axioms joint_kernel_zero
#print axioms joint_injective
#print axioms bottomBasis_apply
#print axioms sharp_dimension
end
end D5.S3.VertexAlgebra.Lattice.ActualZhuJointFaithful
