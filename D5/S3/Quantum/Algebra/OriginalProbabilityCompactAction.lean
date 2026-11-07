/- GID: D5/S3/Quantum/Algebra/OriginalProbabilityCompactAction
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/OriginalProbabilityCompactAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete bounded prediction rows give compact reversible continuation closure. -/

module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Tactic

/-! Complete original prediction rows and their reversible continuations. -/

@[expose] public section

namespace D5.S3.Quantum.Algebra.OriginalProbabilityCompactAction

open Set
noncomputable section
universe u v w x y
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {Γ : Type v} {I : Type w}

private theorem row_preserving_compact
    (row : Γ → V) (read : V →ₗ[ℝ] (I → ℝ))
    (hread : Function.Injective read)
    (hspan : Submodule.span ℝ (Set.range row) = ⊤)
    (hbound : ∀ a i, read (row a) i ∈ Set.Icc (0 : ℝ) 1)
    (S : Subgroup (V →L[ℝ] V)ˣ)
    (hpres : ∀ g : S, ∀ a, ∃ b, g.val.val (row a) = row b) :
    IsCompact (S.topologicalClosure : Set (V →L[ℝ] V)ˣ) := by
  let K : Set V := read ⁻¹' Set.Icc (0 : I → ℝ) 1
  have hK : IsCompact K :=
    (read.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hread)).isCompact_preimage
      isCompact_Icc
  have hrow (a : Γ) : row a ∈ K :=
    ⟨fun i => (hbound a i).1,fun i => (hbound a i).2⟩
  let ev : (V →L[ℝ] V) →ₗ[ℝ] (Γ → V) := {
    toFun T a := T (row a)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hev : Function.Injective ev := by
    intro T U hTU
    apply ContinuousLinearMap.coe_injective
    apply LinearMap.ext_on_range hspan
    intro a
    exact congrFun hTU a
  let C : Set (V →L[ℝ] V) := ev ⁻¹' Set.pi Set.univ (fun _ => K)
  have hC : IsCompact C :=
    (ev.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hev)).isCompact_preimage
      (isCompact_univ_pi fun _ => hK)
  let D : Set (V →L[ℝ] V)ˣ := Units.embedProduct (V →L[ℝ] V) ⁻¹'
    (C ×ˢ (MulOpposite.unop ⁻¹' C))
  have hD : IsCompact D := Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hC.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.mpr hC))
  have hmem (g : S) : g.val.val ∈ C := by
    intro a _
    obtain ⟨b,hb⟩ := hpres g a
    change g.val.val (row a) ∈ K
    rw [hb]
    exact hrow b
  apply hD.of_isClosed_subset S.isClosed_topologicalClosure
  rw [Subgroup.topologicalClosure_coe]
  apply closure_minimal _ hD.isClosed
  intro g hg
  exact ⟨hmem ⟨g,hg⟩,hmem (⟨g,hg⟩ : S)⁻¹⟩

/-- Original full prediction rows determine actual reversible continuation
operators, whose closure in the actual unit group is compact. -/
theorem continuation_compact [Group Γ]
    (row : Γ → V) (read : V →ₗ[ℝ] (I → ℝ))
    (hread : Function.Injective read)
    (hspan : Submodule.span ℝ (Set.range row) = ⊤)
    (hbound : ∀ a i, read (row a) i ∈ Set.Icc (0 : ℝ) 1)
    (futurePrefix : Γ → I → I)
    (hshift : ∀ a g i, read (row (a*g)) i = read (row a) (futurePrefix g i)) :
    ∃ ρ : Γᵐᵒᵖ →* (V →L[ℝ] V)ˣ,
      (∀ a g, (ρ (MulOpposite.op g)).val (row a) = row (a*g)) ∧
      IsCompact (ρ.range.topologicalClosure : Set (V →L[ℝ] V)ˣ) := by
  classical
  have hstable (g : Γ) (x : V) :
      ∃ y : V, read y = fun i => read x (futurePrefix g i) := by
    have hx : x ∈ Submodule.span ℝ (Set.range row) := by rw [hspan]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a,rfl⟩ := hx
      exact ⟨row (a*g),funext (hshift a g)⟩
    | zero => exact ⟨0,by ext i; simp⟩
    | add x y hx hy hix hiy =>
      obtain ⟨x',hx'⟩ := hix
      obtain ⟨y',hy'⟩ := hiy
      exact ⟨x'+y',by ext i; simp [hx',hy']⟩
    | smul r x hx hix =>
      obtain ⟨x',hx'⟩ := hix
      exact ⟨r • x',by ext i; simp [hx']⟩
  let f (g : Γ) (x : V) := (hstable g x).choose
  have hf (g : Γ) (x : V) : read (f g x) = fun i => read x (futurePrefix g i) :=
    (hstable g x).choose_spec
  let T (g : Γ) : V →ₗ[ℝ] V := {
    toFun := f g
    map_add' x y := by
      apply hread
      rw [map_add,hf,hf,hf]
      ext i
      simp only [map_add,Pi.add_apply]
    map_smul' r x := by
      apply hread
      rw [map_smul,hf,hf]
      ext i
      simp only [map_smul,Pi.smul_apply,RingHom.id_apply] }
  have hT (g a : Γ) : T g (row a) = row (a*g) := by
    apply hread
    exact (hstable g (row a)).choose_spec.trans (funext (hshift a g)).symm
  have hT1 : T 1 = LinearMap.id := by
    apply LinearMap.ext_on_range hspan
    intro a
    simpa using hT 1 a
  have hTmul (g h : Γ) : (T g).comp (T h) = T (h*g) := by
    apply LinearMap.ext_on_range hspan
    intro a
    simp only [LinearMap.comp_apply,hT,mul_assoc]
  let E (g : Γ) : V ≃ₗ[ℝ] V := {
    toLinearMap := T g
    invFun := T g⁻¹
    left_inv x := by
      have hh := congrArg (fun f : V →ₗ[ℝ] V => f x) (hTmul g⁻¹ g)
      simpa [hT1] using hh
    right_inv x := by
      have hh := congrArg (fun f : V →ₗ[ℝ] V => f x) (hTmul g g⁻¹)
      simpa [hT1] using hh }
  let ρ : Γᵐᵒᵖ →* (V →L[ℝ] V)ˣ := {
    toFun g := (E g.unop).toContinuousLinearEquiv.toUnit
    map_one' := by
      apply Units.ext
      ext x
      exact congrArg (fun f : V →ₗ[ℝ] V => f x) hT1
    map_mul' g h := by
      apply Units.ext
      ext x
      exact (congrArg (fun f : V →ₗ[ℝ] V => f x)
        (hTmul g.unop h.unop)).symm }
  refine ⟨ρ,fun a g => hT g a,?_⟩
  apply row_preserving_compact row read hread hspan hbound ρ.range
  intro g a
  obtain ⟨k,hk⟩ := g.property
  refine ⟨a*k.unop,?_⟩
  change g.val.val (row a) = _
  rw [← hk]
  exact hT k.unop a


private theorem kernel_representation (H : Subgroup (V →L[ℝ] V)ˣ) [CompactSpace H]
    (mass : V →ₗ[ℝ] ℝ)
    (hpres : ∀ (g : H) v, mass (g.val.val v) = mass v)
    (hfaithful : ∀ g : H, (∀ v : mass.ker, g.val.val v = v) → g = 1) :
    ∃ r : H →* (mass.ker →L[ℝ] mass.ker)ˣ,
      Continuous r ∧ Function.Injective r ∧
      (∀ (g : H) (v : mass.ker), ((r g).val v : V) = g.val.val v) ∧
      IsCompact (r.range : Set (mass.ker →L[ℝ] mass.ker)ˣ) := by
  let T (g : H) : mass.ker →ₗ[ℝ] mass.ker := g.val.val.toLinearMap.restrict (by
    intro v hv
    change mass (g.val.val v) = 0
    rw [hpres]
    exact hv)
  let R (g : H) : mass.ker →L[ℝ] mass.ker := (T g).toContinuousLinearMap
  let r : H →* (mass.ker →L[ℝ] mass.ker)ˣ := {
    toFun g := {
      val := R g
      inv := R g⁻¹
      val_inv := by
        apply ContinuousLinearMap.ext
        intro v
        apply Subtype.ext
        change (g.val*g.val⁻¹).val v = v
        rw [mul_inv_cancel]
        rfl
      inv_val := by
        apply ContinuousLinearMap.ext
        intro v
        apply Subtype.ext
        change (g.val⁻¹*g.val).val v = v
        rw [inv_mul_cancel]
        rfl }
    map_one' := by apply Units.ext; apply ContinuousLinearMap.ext; intro v; apply Subtype.ext; rfl
    map_mul' _ _ := by apply Units.ext; apply ContinuousLinearMap.ext; intro v; apply Subtype.ext; rfl }
  have heval (g : H) (v : mass.ker) : ((r g).val v : V) = g.val.val v := rfl
  let ev : (mass.ker →L[ℝ] mass.ker) →ₗ[ℝ] (mass.ker → mass.ker) := {
    toFun A v := A v
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hev : Function.Injective ev := by
    intro A B h
    apply ContinuousLinearMap.ext
    intro v
    exact congrFun h v
  have hcont : Continuous R := by
    apply (ev.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hev)).toIsEmbedding.continuous_iff.mpr
    apply continuous_pi
    intro v
    apply Continuous.subtype_mk
    change Continuous (fun g : H => g.val.val (v : V))
    fun_prop
  have hr : Continuous r := Units.continuous_iff.mpr ⟨hcont,hcont.comp continuous_inv⟩
  have hinj : Function.Injective r := by
    intro g h hgh
    have hh : r (g⁻¹*h) = 1 := by rw [map_mul,map_inv,hgh,inv_mul_cancel]
    have he : g⁻¹*h = 1 := hfaithful _ (by
      intro v
      have hv := congrArg (fun u : (mass.ker →L[ℝ] mass.ker)ˣ => ((u.val v : mass.ker) : V)) hh
      change ((r (g⁻¹*h)).val v : V) = (v : V) at hv
      rw [heval] at hv
      exact hv)
    exact inv_mul_eq_one.mp he
  exact ⟨r,hr,hinj,heval,isCompact_range hr⟩

/-- The actual compact continuation closure has a normalized fixed center;
its original mass-zero space is cyclic and the restricted action is faithful. -/
theorem centered_continuation [Group Γ]
    (row : Γ → V) (read : V →ₗ[ℝ] (I → ℝ))
    (hread : Function.Injective read)
    (hspan : Submodule.span ℝ (Set.range row) = ⊤)
    (hbound : ∀ a i, read (row a) i ∈ Set.Icc (0 : ℝ) 1)
    (futurePrefix : Γ → I → I)
    (hshift : ∀ a g i, read (row (a*g)) i = read (row a) (futurePrefix g i))
    (mass : V →ₗ[ℝ] ℝ) (hmass : ∀ a, mass (row a) = 1) :
    ∃ ρ : Γᵐᵒᵖ →* (V →L[ℝ] V)ˣ,
      (∀ a g, (ρ (MulOpposite.op g)).val (row a) = row (a*g)) ∧
      IsCompact (ρ.range.topologicalClosure : Set (V →L[ℝ] V)ˣ) ∧
      ∃ c : V, mass c = 1 ∧
        (∀ g : ρ.range.topologicalClosure, g.val.val c = c) ∧
        (∀ (g : ρ.range.topologicalClosure) v, mass (g.val.val v) = mass v) ∧
        Submodule.span ℝ (Set.range (fun a => row a-c)) = mass.ker ∧
        Submodule.span ℝ (Set.range (fun g : ρ.range.topologicalClosure =>
          g.val.val (row 1-c))) = mass.ker ∧
        (mass.ker ≠ ⊥ → row 1-c ≠ 0) ∧
        (∀ g : ρ.range.topologicalClosure,
          (∀ v : mass.ker, g.val.val v = v) → g = 1) ∧
        ∃ r : ρ.range.topologicalClosure →* (mass.ker →L[ℝ] mass.ker)ˣ,
          Continuous r ∧ Function.Injective r ∧
          (∀ (g : ρ.range.topologicalClosure) (v : mass.ker),
            ((r g).val v : V) = g.val.val v) ∧
          IsCompact (r.range : Set (mass.ker →L[ℝ] mass.ker)ˣ) := by
  classical
  obtain ⟨ρ,hρ,hcompact⟩ := continuation_compact row read hread hspan hbound futurePrefix hshift
  let H := ρ.range.topologicalClosure
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hcompact
  letI : MeasurableSpace H := borel H
  letI : BorelSpace H := ⟨rfl⟩
  let μ : MeasureTheory.Measure H := MeasureTheory.Measure.haarMeasure ⊤
  letI : MeasureTheory.IsProbabilityMeasure μ := ⟨MeasureTheory.Measure.haarMeasure_self⟩
  letI : μ.IsMulLeftInvariant := by dsimp [μ]; infer_instance
  let m : V →L[ℝ] ℝ := mass.toContinuousLinearMap
  have hrange : ∀ g : ρ.range, ∀ v, mass (g.val.val v) = mass v := by
    intro g
    obtain ⟨k,hk⟩ := g.property
    have heq : mass.comp (ρ k).val.toLinearMap = mass := by
      apply LinearMap.ext_on_range hspan
      intro a
      change mass ((ρ k).val (row a)) = mass (row a)
      have hh := hρ a k.unop
      simpa only [MulOpposite.op_unop,hmass] using congrArg mass hh
    intro v
    rw [← hk]
    exact LinearMap.congr_fun heq v
  have hclosed : IsClosed {g : (V →L[ℝ] V)ˣ | ∀ v, mass (g.val v) = mass v} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_eq _ continuous_const
    change Continuous (fun g : (V →L[ℝ] V)ˣ => m (g.val v))
    fun_prop
  have hpres : ∀ (g : H) v, mass (g.val.val v) = mass v := by
    have hs : (H : Set (V →L[ℝ] V)ˣ) ⊆
        {g : (V →L[ℝ] V)ˣ | ∀ v, mass (g.val v) = mass v} := by
      change closure (ρ.range : Set (V →L[ℝ] V)ˣ) ⊆ _
      apply closure_minimal _ hclosed
      exact fun g hg => hrange ⟨g,hg⟩
    exact fun g => hs g.property
  let f : H → V := fun g => g.val.val (row 1)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hi : MeasureTheory.Integrable f μ := hf.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace f)
  let c := ∫ g : H, f g ∂μ
  have hc (g : H) : g.val.val c = c := by
    change g.val.val (∫ h, f h ∂μ) = ∫ h, f h ∂μ
    rw [← ContinuousLinearMap.integral_comp_comm _ hi]
    exact MeasureTheory.integral_mul_left_eq_self f g
  have hmc : mass c = 1 := by
    change m (∫ g : H, f g ∂μ) = 1
    rw [← ContinuousLinearMap.integral_comp_comm _ hi]
    have hh : (fun g : H => m (f g)) = fun _ => (1 : ℝ) := by
      funext g
      exact (hpres g (row 1)).trans (hmass 1)
    rw [hh]
    simp
  let P : V →ₗ[ℝ] V := LinearMap.id - mass.smulRight c
  have hP : P.range = mass.ker := by
    ext v
    constructor
    · rintro ⟨w,rfl⟩
      change mass (w-mass w • c) = 0
      simp [hmc]
    · intro hv
      refine ⟨v,?_⟩
      change v - mass v • c = v
      rw [show mass v = 0 from hv,zero_smul,sub_zero]
  have hW : Submodule.span ℝ (Set.range (fun a => row a-c)) = mass.ker := by
    have heq : (fun a => P (row a)) = fun a => row a-c := by
      funext a
      change row a - mass (row a) • c = row a-c
      rw [hmass,one_smul]
    have hh := Submodule.map_span P (Set.range row)
    rw [hspan,Submodule.map_top,← Set.range_comp] at hh
    change P.range = Submodule.span ℝ (Set.range (fun a => P (row a))) at hh
    rw [heq] at hh
    exact hh.symm.trans hP
  have hzero : mass (row 1-c) = 0 := by simp [hmass,hmc]
  have hcyclic : Submodule.span ℝ (Set.range (fun g : H => g.val.val (row 1-c))) = mass.ker := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨g,rfl⟩
      change mass (g.val.val (row 1-c)) = 0
      rw [hpres,hzero]
    · rw [← hW]
      apply Submodule.span_le.mpr
      rintro _ ⟨a,rfl⟩
      let g : H := ⟨ρ (MulOpposite.op a),ρ.range.le_topologicalClosure ⟨_,rfl⟩⟩
      have hg : g.val.val (row 1-c) = row a-c := by
        rw [map_sub,hc]
        simpa using congrArg (fun v : V => v-c) (hρ 1 a)
      change row a-c ∈ Submodule.span ℝ (Set.range (fun g : H => g.val.val (row 1-c)))
      rw [← hg]
      exact Submodule.subset_span ⟨g,rfl⟩
  have hfaithful : ∀ g : H, (∀ v : mass.ker, g.val.val v = v) → g = 1 := by
    intro g hg
    apply Subtype.ext
    apply Units.ext
    ext v
    change g.val.val v = v
    let w : mass.ker := ⟨v-mass v • c,by simp [hmc]⟩
    have hh := hg w
    change g.val.val (v-mass v • c) = v-mass v • c at hh
    rw [map_sub,map_smul,hc] at hh
    simpa only [sub_add_cancel] using congrArg (fun z : V => z+mass v • c) hh
  refine ⟨ρ,hρ,hcompact,c,hmc,hc,hpres,hW,hcyclic,?_,hfaithful,?_⟩
  · intro hnonzero he
    apply hnonzero
    rw [← hcyclic,he]
    simp
  · exact kernel_representation H mass hpres hfaithful


private theorem normalized_prediction_mass {F : Type x} {O : F → Type y} [Nonempty F]
    (row : Γ → V) (read : V →ₗ[ℝ] (I → ℝ))
    (hspan : Submodule.span ℝ (Set.range row) = ⊤)
    (label : ∀ f, O f → I)
    (hnorm : ∀ a f, HasSum (fun j => read (row a) (label f j)) 1) :
    ∃ mass : V →ₗ[ℝ] ℝ, (∀ a, mass (row a) = 1) ∧
      ∀ v f, HasSum (fun j => read v (label f j)) (mass v) := by
  classical
  have hex (v : V) : ∃ m : ℝ, ∀ f, HasSum (fun j => read v (label f j)) m := by
    have hv : v ∈ Submodule.span ℝ (Set.range row) := by rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a,rfl⟩ := hv
      exact ⟨1,hnorm a⟩
    | zero => exact ⟨0,by intro f; simpa using (hasSum_zero : HasSum (fun _ : O f => (0 : ℝ)) 0)⟩
    | add v w hv hw hiv hiw =>
      obtain ⟨m,hm⟩ := hiv
      obtain ⟨n,hn⟩ := hiw
      exact ⟨m+n,fun f => by simpa only [map_add,Pi.add_apply] using (hm f).add (hn f)⟩
    | smul r v hv hiv =>
      obtain ⟨m,hm⟩ := hiv
      exact ⟨r*m,fun f => by simpa only [map_smul,Pi.smul_apply,smul_eq_mul] using (hm f).mul_left r⟩
  let f0 : F := Classical.choice inferInstance
  let m (v : V) := (hex v).choose
  have hm (v : V) (f : F) : HasSum (fun j => read v (label f j)) (m v) := (hex v).choose_spec f
  let mass : V →ₗ[ℝ] ℝ := {
    toFun := m
    map_add' v w := (hm (v+w) f0).unique (by
      simpa only [map_add,Pi.add_apply] using (hm v f0).add (hm w f0))
    map_smul' r v := (hm (r • v) f0).unique (by
      simpa only [map_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply] using (hm v f0).mul_left r) }
  exact ⟨mass,fun a => (hm (row a) f0).unique (hnorm a f0),hm⟩

/-- Nonnegative normalized original tests construct the mass, compact actual
continuations and their faithful cyclic action on the full mass-zero space. -/
theorem probability_frontend [Group Γ] {F : Type x} {O : F → Type y} [Nonempty F]
    (row : Γ → V) (read : V →ₗ[ℝ] (I → ℝ))
    (hread : Function.Injective read)
    (hspan : Submodule.span ℝ (Set.range row) = ⊤)
    (hpos : ∀ a i, 0 ≤ read (row a) i)
    (label : ∀ f, O f → I) (hcover : ∀ i, ∃ f j, label f j = i)
    (hnorm : ∀ a f, HasSum (fun j => read (row a) (label f j)) 1)
    (futurePrefix : Γ → I → I)
    (hshift : ∀ a g i, read (row (a*g)) i = read (row a) (futurePrefix g i)) :
    ∃ mass : V →ₗ[ℝ] ℝ, (∀ a, mass (row a) = 1) ∧
      (∀ v f, HasSum (fun j => read v (label f j)) (mass v)) ∧
    ∃ ρ : Γᵐᵒᵖ →* (V →L[ℝ] V)ˣ,
      (∀ a g, (ρ (MulOpposite.op g)).val (row a) = row (a*g)) ∧
      IsCompact (ρ.range.topologicalClosure : Set (V →L[ℝ] V)ˣ) ∧
      ∃ c : V, mass c = 1 ∧
        (∀ g : ρ.range.topologicalClosure, g.val.val c = c) ∧
        (∀ (g : ρ.range.topologicalClosure) v, mass (g.val.val v) = mass v) ∧
        Submodule.span ℝ (Set.range (fun a => row a-c)) = mass.ker ∧
        Submodule.span ℝ (Set.range (fun g : ρ.range.topologicalClosure =>
          g.val.val (row 1-c))) = mass.ker ∧
        (mass.ker ≠ ⊥ → row 1-c ≠ 0) ∧
        (∀ g : ρ.range.topologicalClosure,
          (∀ v : mass.ker, g.val.val v = v) → g = 1) ∧
        ∃ r : ρ.range.topologicalClosure →* (mass.ker →L[ℝ] mass.ker)ˣ,
          Continuous r ∧ Function.Injective r ∧
          (∀ (g : ρ.range.topologicalClosure) (v : mass.ker),
            ((r g).val v : V) = g.val.val v) ∧
          IsCompact (r.range : Set (mass.ker →L[ℝ] mass.ker)ˣ) := by
  classical
  obtain ⟨mass,hmass,hall⟩ := normalized_prediction_mass row read hspan label hnorm
  have hbound : ∀ a i, read (row a) i ∈ Set.Icc (0 : ℝ) 1 := by
    intro a i
    obtain ⟨f,j,rfl⟩ := hcover i
    refine ⟨hpos a _,?_⟩
    simpa using sum_le_hasSum ({j} : Finset (O f)) (fun k _ => hpos a (label f k)) (hnorm a f)
  exact ⟨mass,hmass,hall,centered_continuation row read hread hspan hbound futurePrefix hshift mass hmass⟩

end
end D5.S3.Quantum.Algebra.OriginalProbabilityCompactAction
