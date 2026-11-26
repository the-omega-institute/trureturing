import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Lattices.EuclideanCommonLattice
import Reg.Support.UniverseSingleReadout

/-! The order comparison readout for the common integral frame inequality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

open Module Finset
open _root_.D5.S3.Combinatorics.Lattices.EuclideanCommonLattice
open _root_.D5.S3.Combinatorics.Lattices.EuclideanSublattices
open _root_.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan
open _root_.D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe uI uV uW uH

namespace Reg.D5.S3.Combinatorics.Lattices.EuclideanCommonLattice

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def law (Vread : Realization signature) : Prop := ∀ {I : Type uI} [Fintype I] (V : I → Type uV)
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)]
    [∀ i, FiniteDimensional ℝ (V i)]
    {W : Type uW} {H : Type uH} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (N : ∀ i, Submodule ℤ (V i)) (C : Submodule ℤ W)
    [∀ i, DiscreteTopology (N i)] [DiscreteTopology C]
    (_hN : ∀ i, Submodule.span ℝ (N i : Set (V i)) = ⊤)
    (B : ∀ i, V i →L[ℝ] W) (A : ∀ i, V i →ₗ[ℝ] H)
    (P : H →ₗ[ℝ] W) (_hP : Function.Surjective P)
    (_hPA : ∀ i, P ∘ₗ A i = (B i).toLinearMap)
    (_hBC : ∀ i x, x ∈ N i → B i x ∈ C)
    (h : I → ℝ) (_hB : ∀ i, B i ≠ 0 → Real.log ‖B i‖ ≤ h i)
    (c : I → ℝ) (s u Hmax e η : ℝ)
    (_hR : 0 < ∑ i, (finrank ℝ (V i) : ℝ))
    (_hH : 0 ≤ Hmax) (_he1 : e < 1) (_hd : 0 < finrank ℝ W)
    (_hav : (∑ i, (finrank ℤ (N i) : ℝ)) * s ≤
      ∑ i, (finrank ℤ (N i) : ℝ) * (latticeSlope (N i) - h i))
    (_hmax : ∀ i, 0 < finrank ℤ (N i) →
      (slopeData (N i)).muMax ⊥ ⊤ - h i ≤ s + u)
    (_hlow : s - (slopeData C).muMin ⊥ ⊤ ≤ Hmax)
    (_hgram : ∑ i, hs2 (gram (c i) (A i) - LinearMap.id) ≤
      e * ∑ i, (finrank ℝ (V i) : ℝ))
    (_hframe : LinearMap.trace ℝ H (frame c A ∘ₗ frame c A) ≤
      (1 + η) * (LinearMap.trace ℝ H (frame c A)) ^ 2 / finrank ℝ H),
    Vread.readout () () (s - latticeSlope C) ((finrank ℝ H : ℝ) / finrank ℝ W *
      (4 * u * Real.log (1 + Hmax / u) + (η + 4 * Real.sqrt e) * Hmax)) ∧
    (finrank ℤ C : ℝ) * (s - latticeSlope C) +
      ((finrank ℝ W : ℝ) - finrank ℤ C) * Hmax ≤ finrank ℝ H *
        (4 * u * Real.log (1 + Hmax / u) + (η + 4 * Real.sqrt e) * Hmax) ∧
    ∀ δ : ℝ, δ < 1 → (1 - δ) * finrank ℝ H ≤ (finrank ℝ W : ℝ) →
      s - latticeSlope C ≤
        (4 * u * Real.log (1 + Hmax / u) + (η + 4 * Real.sqrt e) * Hmax) / (1 - δ)

abbrev arena : Arena where
  signature := signature
  Law := law.{uI,uV,uW,uH}

private theorem unit_covolume {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    covolume (Submodule.span ℤ (Set.range b.toBasis)) = 1 := by
  classical
  let ib := Basis.span (b.toBasis.linearIndependent.restrict_scalars' ℤ)
  rw [covolume_eq_gram _ ib]
  have hval : (fun i => (ib i : E)) = b := by
    funext i
    change ((Basis.span (b.toBasis.linearIndependent.restrict_scalars' ℤ)) i : E) = b.toBasis i
    exact Basis.coe_span_apply _ i
  have hgram : Matrix.gram ℝ (fun i => (ib i : E)) = 1 := by
    rw [hval]
    exact Matrix.gram_eq_one_iff_orthonormal.mpr b.orthonormal
  rw [hgram, Matrix.det_one]
  norm_num

private theorem rejected_fails : ¬ arena.{uI,uV,uW,uH}.Law rejected := by
  classical
  intro law
  let I := ULift.{uI} Unit
  let E := EuclideanSpace ℝ (ULift.{uV} Unit)
  let W := EuclideanSpace ℝ (ULift.{uW} Unit)
  let H := EuclideanSpace ℝ (ULift.{uH} Unit)
  let v := EuclideanSpace.basisFun (ULift.{uV} Unit) ℝ
  let w := EuclideanSpace.basisFun (ULift.{uW} Unit) ℝ
  let z := EuclideanSpace.basisFun (ULift.{uH} Unit) ℝ
  let f := v.equiv w (Equiv.ulift.trans Equiv.ulift.symm)
  let g := v.equiv z (Equiv.ulift.trans Equiv.ulift.symm)
  let p := g.symm.trans f
  let N := Submodule.span ℤ (Set.range v.toBasis)
  let C := Submodule.span ℤ (Set.range w.toBasis)
  have hN : Submodule.span ℝ (N : Set E) = ⊤ := by
    simp only [N, Submodule.span_span_of_tower, v.toBasis.span_eq]
  have hPA : p.toLinearMap ∘ₗ g.toLinearMap = f.toLinearMap := by
    ext x
    simp [p]
  have hBC : ∀ x ∈ N, f x ∈ C := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨_, (v.equiv_apply_basis w _ i).symm⟩
    | zero => simpa using C.zero_mem
    | add x y _ _ ihx ihy => simpa using C.add_mem ihx ihy
    | smul n x _ ih => simpa using C.smul_mem n ih
  have hn : ‖f.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ Real.exp 0 := by
    rw [Real.exp_zero]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  have hcov : covolume N = 1 := unit_covolume v
  have hNs : latticeSlope N = 0 := by simp only [latticeSlope, hcov, Real.log_one,
    neg_zero, zero_div]
  have hg1 : g.toLinearMap.adjoint ∘ₗ g.toLinearMap = LinearMap.id := by
    rw [g.adjoint_toLinearMap_eq_symm]
    ext x
    simp
  have hg2 : g.toLinearMap ∘ₗ g.toLinearMap.adjoint = LinearMap.id := by
    rw [g.adjoint_toLinearMap_eq_symm]
    ext x
    simp
  let u := |(slopeData N).muMax ⊥ ⊤| + 1
  let Hmax := |(slopeData C).muMin ⊥ ⊤| + 1
  have hmax : (slopeData N).muMax ⊥ ⊤ - 0 ≤ 0 + u := by
    dsimp [u]
    linarith [le_abs_self ((slopeData N).muMax ⊥ ⊤)]
  have hlow : 0 - (slopeData C).muMin ⊥ ⊤ ≤ Hmax := by
    dsimp [Hmax]
    linarith [neg_le_abs ((slopeData C).muMin ⊥ ⊤)]
  have impossible := law (fun _ : I => E) (fun _ => N) C (fun _ => hN)
    (fun _ => f.toContinuousLinearEquiv.toContinuousLinearMap) (fun _ => g.toLinearMap)
    p.toLinearMap p.surjective (fun _ => hPA) (fun _ => hBC)
    (fun _ => 0) (fun _ hBi =>
      (Real.log_le_iff_le_exp (norm_pos_iff.mpr hBi)).mpr hn) (fun _ => 1)
    0 u Hmax 0 0
    (by simp [I, E]) (by dsimp [Hmax]; positivity)
    (by norm_num) (by simp [W])
    (by simp [hNs]) (fun _ _ => hmax) hlow
    (by simp [gram, hg1, hs2])
    (by simp [frame, hg2, I, H])
  exact impossible.1

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
  norm_num at hh

def statement : Prop := type_of% @common_lattice_slope.{uI,uV,uW,uH}

def family : Registration arena.{uI,uV,uW,uH} statement.{uI,uV,uW,uH} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@common_lattice_slope.{uI,uV,uW,uH}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{uI,uV,uW,uH}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@common_lattice_slope.{uI,uV,uW,uH}) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.EuclideanCommonLattice.common_lattice_slope
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.EuclideanCommonLattice.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{uI,uV,uW,uH}⟩
  objectArena := .source ⟨arena.{uI,uV,uW,uH}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{uI,uV,uW,uH} ⟨family.{uI,uV,uW,uH}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.EuclideanCommonLattice
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.EuclideanCommonLattice

universe u v w z q

namespace Reg.D5.S3.Combinatorics.Lattices.EuclideanCommonLattice.Spectral

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law T := ∀ {I : Type*} [Fintype I] {V : I → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)]
    [∀ i, FiniteDimensional ℝ (V i)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] {J : I → Type*} [∀ i, Fintype (J i)]
    {K : Type*} [Fintype K] (c : I → ℝ) (A : ∀ i, V i →ₗ[ℝ] H)
    (x : ∀ i, J i → ℝ) (y : K → ℝ) (s u Hmax e η : ℝ)
    (flags : SpectralFlags V H A J K x y s Hmax)
    (hR : 0 < ∑ i, (finrank ℝ (V i) : ℝ))
    (hH : 0 ≤ Hmax) (he1 : e < 1)
    (hK : 0 < Fintype.card K)
    (hav : (∑ i, (Fintype.card (J i) : ℝ)) * s ≤ ∑ i, ∑ j, x i j)
    (hmax : ∀ i j, x i j ≤ s + u) (hlow : ∀ j, s - Hmax ≤ y j)
    (hgram : ∑ i, hs2 (gram (c i) (A i) - LinearMap.id) ≤
      e * ∑ i, (finrank ℝ (V i) : ℝ))
    (hframe : LinearMap.trace ℝ H (frame c A ∘ₗ frame c A) ≤
      (1 + η) * (LinearMap.trace ℝ H (frame c A)) ^ 2 / finrank ℝ H),
    (∑ j, max (s - y j) 0) ≤ finrank ℝ H *
      (4 * u * Real.log (1 + Hmax / u) + (η + 4 * T.readout () () e) * Hmax) ∧
    s - (∑ j, y j) / Fintype.card K ≤ (finrank ℝ H : ℝ) / Fintype.card K *
      (4 * u * Real.log (1 + Hmax / u) + (η + 4 * Real.sqrt e) * Hmax)

private theorem rejected_fails : ¬ arena.{u,v,w,z,q}.Law rejected := by
  classical
  intro law
  let I := ULift.{u} Unit
  let V := EuclideanSpace ℝ (ULift.{v} Unit)
  let H := EuclideanSpace ℝ (ULift.{w} Unit)
  let J := ULift.{z} Unit
  let K := ULift.{q} Unit
  let iso : V ≃ₗᵢ[ℝ] H := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    ((Equiv.ulift : ULift.{v} Unit ≃ Unit).trans
      (Equiv.ulift : ULift.{w} Unit ≃ Unit).symm)
  let A : V →ₗ[ℝ] H := iso.toLinearMap
  have hleft : A.adjoint ∘ₗ A = LinearMap.id := by
    rw [show A.adjoint = iso.symm.toLinearMap from iso.adjoint_toLinearMap_eq_symm]
    apply LinearMap.ext
    intro x
    change iso.symm (iso x) = x
    exact iso.symm_apply_apply x
  have hright : A ∘ₗ A.adjoint = LinearMap.id := by
    rw [show A.adjoint = iso.symm.toLinearMap from iso.adjoint_toLinearMap_eq_symm]
    apply LinearMap.ext
    intro x
    change iso (iso.symm x) = x
    exact iso.apply_symm_apply x
  let flags : SpectralFlags (fun _ : I => V) H (fun _ => A)
      (fun _ => J) K (fun _ _ => 0) (fun _ => 0) 0 1 := {
    source := fun _ _ => ⊤
    target := fun _ => ⊤
    source_dim := by intro i; simp [J, V]
    source_codim := by
      intro t ht i
      simp [not_lt.mpr (neg_nonpos.mpr ht.1)]
    target_codim := by
      intro t ht
      simp [not_lt.mpr (neg_nonpos.mpr ht.1)]
    placement := by intro t ht i; exact le_top }
  have h := law (I := I) (V := fun _ : I => V) (H := H)
    (J := fun _ : I => J) (K := K) (fun _ => 1) (fun _ => A)
    (fun _ _ => 0) (fun _ => 0) 0 0 1 0 0 flags
    (by simp [I, V]) (by norm_num)
    (by norm_num) (by simp [K]) (by simp) (by simp) (by norm_num)
    (by simp [gram, hleft, hs2])
    (by simp [frame, hright, I, H, LinearMap.trace_id])
  have impossible := h.1
  norm_num [rejected, realize, H] at impossible

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨(), 0, 1, by change Real.sqrt 0 ≠ Real.sqrt 1; norm_num⟩

def family : Registration arena.{u,v,w,z,q}
    (type_of% @spectral_frame_slope.{u,v,w,z,q}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@spectral_frame_slope.{u,v,w,z,q}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u,v,w,z,q}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@spectral_frame_slope.{u,v,w,z,q}) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.EuclideanCommonLattice.spectral_frame_slope
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.EuclideanCommonLattice.Spectral.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,z,q}⟩
  objectArena := .source ⟨arena.{u,v,w,z,q}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u,v,w,z,q} ⟨family.{u,v,w,z,q}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.EuclideanCommonLattice
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "arg", "arg", "arg", "arg", "fn", "arg",
        "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.EuclideanCommonLattice.Spectral
