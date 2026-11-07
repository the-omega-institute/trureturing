/- GID: D5/S3/VertexAlgebra/Analysis/OriginalSmearingCore
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Analysis/OriginalSmearingCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-carrier graph approximation and charge transport for smooth smearing. -/

import D5.S3.VertexAlgebra.Analysis.OriginalSmoothDomain

/-!
The core is for the minimal closure of the actual smeared field on H_infinity.
It is not a core assertion for its maximal adjoint. Opposite formal adjoints
supply closed extensions and closability, not equality of adjoint closures.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators InnerProductSpace Topology VertexOperator
namespace D5.S3.VertexAlgebra.Analysis.OriginalSmearing
open LatticeGeneratingFieldLocality LatticeAllStateField LatticePositiveEnergy SmoothCircleFourier
open private chargeSpace word_charge from
  D5.S3.VertexAlgebra.Sectors.LatticeSectorIntertwiner
open private inclusion_injective projection_embed projection_inclusion truncation_algebraic truncation_tendsto from
  D5.S3.VertexAlgebra.Analysis.OriginalSobolev
open private modeExtension_embed from
  D5.S3.VertexAlgebra.Analysis.OriginalModeExtension
open private smear_apply vector_summable from
  D5.S3.VertexAlgebra.Analysis.OriginalInfiniteSmearing
open private finite_in_domain field_eval smoothDomain_dense field_formal
  field_le_opposite_adjoint field_closable from
  D5.S3.VertexAlgebra.Analysis.OriginalSmoothDomain

open Model

variable (M : Model)

def Model.finiteDomain : Submodule ℂ M.Hilbert := (M.embed 0).range

def Model.finiteDomainEquiv : Carrier M.D ≃ₗ[ℂ] M.finiteDomain :=
  LinearEquiv.ofInjective (M.embed 0) (embed_injective M 0)

private theorem finiteDomainEquiv_coe (v : Carrier M.D) :
    (M.finiteDomainEquiv v : M.Hilbert) = M.embed 0 v := rfl

/-- Restriction to the original finite input carrier, with Hilbert-valued output. -/
def Model.finiteField (a : Charge M.D) (f : Test) : M.Hilbert →ₗ.[ℂ] M.Hilbert where
  domain := M.finiteDomain
  toFun := (M.smear a f 0).toLinearMap.comp
    ((M.embed (M.order a)).comp M.finiteDomainEquiv.symm.toLinearMap)

private theorem finiteField_eval (a : Charge M.D) (f : Test) (v : Carrier M.D) :
    M.finiteField a f (M.finiteDomainEquiv v) =
      M.smear a f 0 (M.embed (M.order a) v) := by
  change M.smear a f 0
    (M.embed _ (M.finiteDomainEquiv.symm (M.finiteDomainEquiv v))) = _
  rw [M.finiteDomainEquiv.symm_apply_apply]
  simp only [Nat.add_zero]

private theorem finiteField_le (a : Charge M.D) (f : Test) :
    M.finiteField a f ≤ M.field a f := by
  constructor
  · rintro z ⟨v,rfl⟩
    exact finite_in_domain M v
  · intro u v huv
    let z := M.finiteDomainEquiv.symm u
    have hu : M.finiteDomainEquiv z = u := M.finiteDomainEquiv.apply_symm_apply u
    have hv : M.domainEquiv (M.finiteFamily z) = v := by
      apply Subtype.ext
      exact (congrArg Subtype.val hu).trans huv
    rw [← hu, ← hv, finiteField_eval, field_eval]
    rfl

private theorem field_graph_approximated (a : Charge M.D) (f : Test) :
    M.field a f ≤ (M.finiteField a f).closure := by
  let B : M.Sobolev (M.order a) →L[ℂ] M.Hilbert × M.Hilbert :=
    (M.inclusion 0 (M.order a) (Nat.zero_le _)).prod (M.smear a f 0)
  have hfin := (field_closable M a f).leIsClosable (finiteField_le M a f)
  have hmem (x : M.Sobolev (M.order a)) :
      B x ∈ (M.finiteField a f).closure.graph := by
    apply hfin.closure_isClosed.mem_of_tendsto
      ((B.continuous.tendsto x).comp (truncation_tendsto M (M.order a) x))
    apply Filter.Eventually.of_forall
    intro F
    obtain ⟨v,hv⟩ := truncation_algebraic M (M.order a) F x
    change B (M.truncation (M.order a) F x) ∈ (M.finiteField a f).closure.graph
    rw [hv]
    apply LinearPMap.le_graph_of_le (LinearPMap.le_closure (M.finiteField a f))
    have hh := (M.finiteField a f).mem_graph (M.finiteDomainEquiv v)
    rw [finiteField_eval, finiteDomainEquiv_coe] at hh
    simpa only [B, ContinuousLinearMap.prod_apply, inclusion_embed] using hh
  apply LinearPMap.le_of_le_graph
  rintro z hz
  obtain ⟨u,hu,hf⟩ := (LinearPMap.mem_graph_iff (M.field a f)).mp hz
  let x := M.domainEquiv.symm u
  have hx : M.domainEquiv x = u := M.domainEquiv.apply_symm_apply u
  have hz' : z = B (x.1 (M.order a)) := by
    apply Prod.ext
    · exact hu.symm.trans (by
        rw [← hx]
        exact (x.2 0 _ (Nat.zero_le _)).symm)
    · exact hf.symm.trans (by rw [← hx, field_eval]; rfl)
  rw [hz']
  exact hmem _

private theorem field_closure_eq (a : Charge M.D) (f : Test) :
    (M.field a f).closure = (M.finiteField a f).closure := by
  have hc := field_closable M a f
  have hf := hc.leIsClosable (finiteField_le M a f)
  have hid : (M.finiteField a f).closure.closure = (M.finiteField a f).closure := by
    apply LinearPMap.eq_of_eq_graph
    rw [← hf.closure_isClosed.isClosable.graph_closure_eq_closure_graph,
      hf.closure_isClosed.submodule_topologicalClosure_eq]
  apply le_antisymm
  · simpa only [hid] using
      hf.closure_isClosed.isClosable.closure_mono (field_graph_approximated M a f)
  · exact hc.closure_mono (finiteField_le M a f)

private theorem finite_carrier_core (a : Charge M.D) (f : Test) :
    (M.field a f).closure.HasCore M.finiteDomain := by
  rw [field_closure_eq]
  exact LinearPMap.closureHasCore (M.finiteField a f)

/-- Closure of the original charge sector in each actual Sobolev completion. -/
def Model.chargeSector (k : ℕ) (δ : Charge M.D) : Submodule ℂ (M.Sobolev k) :=
  ((M.embed k).comp (Finsupp.lsingle δ)).range.topologicalClosure

private theorem chargeSector_closed (k : ℕ) (δ : Charge M.D) :
    IsClosed (M.chargeSector k δ : Set (M.Sobolev k)) :=
  Submodule.isClosed_topologicalClosure _

private theorem mode_charge (a δ : Charge M.D) (m : ℤ) (p : Oscillator M.D) :
    M.mode a m (Finsupp.single δ p) ∈ chargeSpace M.D (a+δ) := by
  simpa only [mode, wordField] using
    word_charge M.D a δ [] (m + chargeEnergy M.D a - 1) p

private theorem mode_sector_finite (a δ : Charge M.D) (k : ℕ) (m : ℤ)
    (p : Oscillator M.D) :
    M.modeExtension a k m (M.embed (M.order a+k) (Finsupp.single δ p)) ∈
      M.chargeSector k (a+δ) := by
  rw [modeExtension_embed]
  obtain ⟨q,hq⟩ := mode_charge M a δ m p
  exact (((M.embed k).comp (Finsupp.lsingle (a+δ))).range).le_topologicalClosure
    ⟨q, congrArg (M.embed k) hq⟩

private theorem mode_sector (a δ : Charge M.D) (k : ℕ) (m : ℤ)
    (x : M.Sobolev (M.order a+k)) (hx : x ∈ M.chargeSector (M.order a+k) δ) :
    M.modeExtension a k m x ∈ M.chargeSector k (a+δ) := by
  have hmap : Set.MapsTo (M.modeExtension a k m)
      (((M.embed (M.order a+k)).comp (Finsupp.lsingle δ)).range :
        Set (M.Sobolev (M.order a+k)))
      (M.chargeSector k (a+δ) : Set (M.Sobolev k)) := by
    rintro z ⟨p,rfl⟩
    exact mode_sector_finite M a δ k m p
  change x ∈ closure (((M.embed (M.order a+k)).comp (Finsupp.lsingle δ)).range :
    Set (M.Sobolev (M.order a+k))) at hx
  exact hmap.closure_left (M.modeExtension a k m).continuous
    (chargeSector_closed M k (a+δ)) hx

private theorem smear_sector (a δ : Charge M.D) (f : Test) (k : ℕ)
    (x : M.Sobolev (M.order a+k)) (hx : x ∈ M.chargeSector (M.order a+k) δ) :
    M.smear a f k x ∈ M.chargeSector k (a+δ) := by
  rw [smear_apply]
  apply (chargeSector_closed M k (a+δ)).mem_of_tendsto
    (vector_summable M a f k x).hasSum
  apply Filter.Eventually.of_forall
  intro F
  apply Submodule.sum_mem
  intro m hm
  exact (M.chargeSector k (a+δ)).smul_mem _ (mode_sector M a δ k m x hx)

/-- The smooth part of a closed original charge sector, component by component. -/
def Model.smoothChargeSector (δ : Charge M.D) : Submodule ℂ M.Smooth where
  carrier x := ∀ k, x.1 k ∈ M.chargeSector k δ
  zero_mem' := fun k => Submodule.zero_mem _
  add_mem' := by
    intro x y hx hy k
    exact Submodule.add_mem _ (hx k) (hy k)
  smul_mem' := by
    intro c x hx k
    exact Submodule.smul_mem _ c (hx k)

private theorem smooth_charge_transport (a δ : Charge M.D) (f : Test) (x : M.Smooth)
    (hx : x ∈ M.smoothChargeSector δ) :
    M.smearFamily a f x ∈ M.smoothChargeSector (a+δ) := by
  change ∀ k, x.1 k ∈ M.chargeSector k δ at hx
  change ∀ k, (M.smearFamily a f x).1 k ∈ M.chargeSector k (a+δ)
  intro k
  exact smear_sector M a δ f k (x.1 _) (hx _)


private theorem gradeProjection_charge (δ : Charge M.D) (n : ℤ) (p : Oscillator M.D) :
    gradeProjection M.D n (Finsupp.single δ p) ∈ chargeSpace M.D δ := by
  classical
  let v := gradeProjection M.D n (Finsupp.single δ p)
  refine ⟨v δ, ?_⟩
  ext b e
  by_cases hb : b = δ
  · subst b
    simp only [Finsupp.lsingle_apply, Finsupp.single_eq_same, v]
  · change (Finsupp.single δ (v δ) b).coeff e = (v b).coeff e
    rw [Finsupp.single_eq_of_ne hb]
    change (0 : Oscillator M.D).coeff e =
      carrierCoeffEquiv M.D (gradeProjection M.D n (Finsupp.single δ p)) (b,e)
    rw [gradeProjection_coeff]
    simp [carrierCoeffEquiv, Finsupp.single_eq_of_ne hb]

private def chargeGrade (δ : Charge M.D) (n : ℤ) : Submodule ℂ (Carrier M.D) :=
  chargeSpace M.D δ ⊓ grade M.D n

private def chargeGradeMap (k : ℕ) (δ : Charge M.D) (n : ℤ) :
    chargeGrade M δ n →ₗ[ℂ] M.Sobolev k := (M.embed k).comp (chargeGrade M δ n).subtype

private theorem chargeGrade_finite (δ : Charge M.D) (n : ℤ) :
    FiniteDimensional ℂ (chargeGrade M δ n) := by
  letI := grade_finiteDimensional M.D M.positive n
  let i : chargeGrade M δ n →ₗ[ℂ] grade M.D n :=
    { toFun := fun x => ⟨x, x.2.2⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact FiniteDimensional.of_injective i (by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : grade M.D n => (z : Carrier M.D)) h)

private theorem projection_sector_grade (δ : Charge M.D) (n : ℤ) (x : M.Hilbert)
    (hx : x ∈ M.chargeSector 0 δ) :
    M.projection 0 n x ∈ (chargeGradeMap M 0 δ n).range := by
  letI := chargeGrade_finite M δ n
  have hclosed : IsClosed ((chargeGradeMap M 0 δ n).range : Set M.Hilbert) :=
    Submodule.closed_of_finiteDimensional _
  have hpre := hclosed.preimage (M.projection 0 n).continuous
  have hsub : ((M.embed 0).comp (Finsupp.lsingle δ)).range ≤
      (chargeGradeMap M 0 δ n).range.comap (M.projection 0 n).toLinearMap := by
    rintro z ⟨p,rfl⟩
    simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe,
      LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [projection_embed]
    refine ⟨⟨gradeProjection M.D n (Finsupp.single δ p),
      gradeProjection_charge M δ n p, gradeProjection_mem M.D n _⟩, rfl⟩
  exact (Submodule.topologicalClosure_minimal _ hsub hpre) hx

private theorem inclusion_reflects_sector (k : ℕ) (δ : Charge M.D) (x : M.Sobolev k)
    (hx : M.inclusion 0 k (Nat.zero_le k) x ∈ M.chargeSector 0 δ) :
    x ∈ M.chargeSector k δ := by
  have hp (n : ℤ) : M.projection k n x ∈ M.chargeSector k δ := by
    obtain ⟨v,hv⟩ := projection_sector_grade M δ n _ hx
    have he : M.projection k n x = M.embed k (v : Carrier M.D) := by
      apply inclusion_injective M 0 k (Nat.zero_le k)
      rw [projection_inclusion, inclusion_embed]
      exact hv.symm
    rw [he]
    obtain ⟨p,hp⟩ := v.2.1
    apply Submodule.le_topologicalClosure
    exact ⟨p, congrArg (M.embed k) hp⟩
  apply (chargeSector_closed M k δ).mem_of_tendsto (truncation_tendsto M k x)
  apply Filter.Eventually.of_forall
  intro F
  simp only [truncation, ContinuousLinearMap.sum_apply]
  apply Submodule.sum_mem (M.chargeSector k δ)
  exact fun n _ => hp n

private theorem smooth_sector_iff (δ : Charge M.D) (x : M.Smooth) :
    x ∈ M.smoothChargeSector δ ↔ M.evaluation x ∈ M.chargeSector 0 δ := by
  change (∀ k, x.1 k ∈ M.chargeSector k δ) ↔ _
  constructor
  · exact fun hx => hx 0
  · intro hx k
    apply inclusion_reflects_sector M k δ (x.1 k)
    rw [x.2 0 k (Nat.zero_le k)]
    exact hx

private theorem field_charge_transport (a δ : Charge M.D) (f : Test)
    (u : M.smoothDomain) (hu : (u : M.Hilbert) ∈ M.chargeSector 0 δ) :
    M.field a f u ∈ M.chargeSector 0 (a+δ) := by
  let x := M.domainEquiv.symm u
  have he : M.domainEquiv x = u := M.domainEquiv.apply_symm_apply u
  have hu0 : (u : M.Hilbert) = M.evaluation x := (congrArg Subtype.val he).symm
  have hx : x ∈ M.smoothChargeSector δ :=
    (smooth_sector_iff M δ x).mpr (hu0 ▸ hu)
  have hout := (smooth_sector_iff M (a+δ) (M.smearFamily a f x)).mp
    (smooth_charge_transport M a δ f x hx)
  rw [← he, field_eval]
  exact hout

end D5.S3.VertexAlgebra.Analysis.OriginalSmearing
