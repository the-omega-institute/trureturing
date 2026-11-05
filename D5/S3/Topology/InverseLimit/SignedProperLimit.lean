/- GID: D5/S3/Topology/InverseLimit/SignedProperLimit
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedProperLimit
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Literal coordinate limits and joint signed proper-stage preservation. -/

import D5.S3.Topology.InverseLimit.CountableJointFusion
import D5.S3.Topology.Measures.ClopenCauchyConvergence
import D5.S3.Topology.Measures.NormPreservingLiftExistence
import D5.S1.Dynamics.Shadowing.MittagLefflerInverseLimit
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Category.Profinite.Limits
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Data.Nat.Nth

/-! The literal proper coordinate limit retains every eligible signed A–F obligation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory CategoryTheory CategoryTheory.Limits Opposite
open scoped Topology Ordinal ENNReal

namespace D5.S3.Topology.InverseLimit.SignedProperLimit

abbrev Coord (a : Ordinal.{0}) := Set.Iio a
abbrev Cube (a : Ordinal.{0}) := Coord a → Bool
/-- Birth enumerations keep even the not-yet-eligible measure labels. -/
abbrev Label := Set.Iio (ω₁ : Ordinal.{0})

/-- Literal coordinate restriction, including finite and countable stages. -/
def restrict {b a : Ordinal.{0}} (h : b ≤ a) (x : Cube a) : Cube b :=
  fun i => x ⟨i.1, lt_of_lt_of_le i.2 h⟩

/-- The input contains only already constructed stages and actual restrictions. -/
structure Prefix (l : Ordinal.{0}) where
  carrier : (a : Coord l) → Set (Cube a.1)
  closed : ∀ a, IsClosed (carrier a)
  nonempty : ∀ a, (carrier a).Nonempty
  compatible : ∀ (a b : Coord l) (h : a ≤ b) (x : carrier b),
    restrict h x.1 ∈ carrier a
  onto : ∀ (a b : Coord l) (h : a ≤ b) (y : carrier a),
    ∃ x : carrier b, restrict h x.1 = y.1

namespace Prefix

variable {l : Ordinal.{0}} (H : Prefix l)

abbrev Space (a : Coord l) := H.carrier a

instance spaceCompact (a : Coord l) : CompactSpace (H.Space a) :=
  (H.closed a).isClosedEmbedding_subtypeVal.compactSpace

instance spaceNonempty (a : Coord l) : Nonempty (H.Space a) := (H.nonempty a).to_subtype

/-- The inherited transition has exactly the old coordinate restriction. -/
def map (a b : Coord l) (h : a ≤ b) : C(H.Space b, H.Space a) where
  toFun x := ⟨restrict h x.1, H.compatible a b h x⟩
  continuous_toFun :=
    ((Pi.continuous_precomp' _).comp continuous_subtype_val).subtype_mk _

/-- Diagram on all earlier stages, including the finite initial segment. -/
def diagram : (Coord l)ᵒᵖ ⥤ Profinite.{1} where
  obj a := Profinite.of (H.Space a.unop)
  map f := CompHausLike.ofHom _ (H.map _ _ (leOfHom f.unop))
  map_id _ := by ext x i; rfl
  map_comp _ _ := by ext x i; rfl

/-- The new space is a literal subset of the original coordinate cube. -/
def limitCarrier : Set (Cube l) :=
  {x | ∀ a : Coord l, restrict (le_of_lt a.2) x ∈ H.carrier a}

abbrev LimitSpace := H.limitCarrier

private theorem limit_closed : IsClosed H.limitCarrier := by
  change IsClosed {x : Cube l | ∀ a : Coord l, restrict (le_of_lt a.2) x ∈ H.carrier a}
  simp only [ofPred_forall]
  exact isClosed_iInter fun a => (H.closed a).preimage (Pi.continuous_precomp' _)

instance limitCompact : CompactSpace H.LimitSpace :=
  H.limit_closed.isClosedEmbedding_subtypeVal.compactSpace

/-- Every limit projection is the literal coordinate restriction. -/
def projection (a : Coord l) : C(H.LimitSpace, H.Space a) where
  toFun x := ⟨restrict (le_of_lt a.2) x.1, x.2 a⟩
  continuous_toFun :=
    ((Pi.continuous_precomp' _).comp continuous_subtype_val).subtype_mk _

/-- The actual coordinate cone. -/
def cone : Cone H.diagram where
  pt := Profinite.of H.LimitSpace
  π :=
    { app := fun a => CompHausLike.ofHom _ (H.projection a.unop)
      naturality := by intro a b f; ext x i; rfl }

/-- Gluing is explicit: coordinate ξ is read at the earlier stage succ ξ. -/
def coneIsLimit (hl : Order.IsSuccLimit l) : IsLimit H.cone := by
  let stage : Coord l → Coord l := fun i => ⟨Order.succ i.1, hl.succ_lt i.2⟩
  let ix : (i : Coord l) → Coord (stage i).1 := fun i => ⟨i.1, Order.lt_succ i.1⟩
  let g : (S : Cone H.diagram) → S.pt → Cube l :=
    fun S x i => (S.π.app (op (stage i)) x).1 (ix i)
  have hg : ∀ (S : Cone H.diagram) (x : S.pt) (a : Coord l),
      restrict (le_of_lt a.2) (g S x) = (S.π.app (op a) x).1 := by
    intro S x a
    funext i
    let ii : Coord l := ⟨i.1, show i.1 < l from lt_trans i.2 a.2⟩
    have hia : stage ii ≤ a := by
      change Order.succ i.1 ≤ a.1
      exact Order.succ_le_of_lt i.2
    let f : op a ⟶ op (stage ii) := (homOfLE hia).op
    have he := ConcreteCategory.congr_hom (S.w f) x
    exact (congrArg (fun y : H.Space (stage ii) => y.1 (ix ii)) he).symm
  refine
    { lift := fun S => CompHausLike.ofHom _
        { toFun := fun x => ⟨g S x, fun a => (hg S x a).symm ▸ (S.π.app (op a) x).2⟩
          continuous_toFun := by
            apply Continuous.subtype_mk
            apply continuous_pi
            intro i
            exact (continuous_apply (ix i)).comp
              (continuous_subtype_val.comp (S.π.app (op (stage i))).hom.hom.continuous) }
      fac := ?_
      uniq := ?_ }
  · intro S a
    apply ConcreteCategory.hom_ext
    intro x
    exact Subtype.ext (hg S x a.unop)
  · intro S m hm
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    funext i
    have he := ConcreteCategory.congr_hom (hm (op (stage i))) x
    exact congrArg (fun y : H.Space (stage i) => y.1 (ix i)) he

/-- Compact full-thread lifting proves onto restriction at the constructed cone. -/
theorem projection_surjective (hl : Order.IsSuccLimit l) (a : Coord l) :
    Function.Surjective (H.projection a) := by
  letI : Nonempty (Coord l) := ⟨a⟩
  intro y
  let T := H.diagram ⋙ Profinite.toTopCat
  letI : ∀ j, Nonempty (T.obj j) := fun j => inferInstanceAs (Nonempty (H.Space j.unop))
  letI : ∀ j, CompactSpace (T.obj j) := fun j => inferInstanceAs (CompactSpace (H.Space j.unop))
  letI : ∀ j, T2Space (T.obj j) := fun j => inferInstanceAs (T2Space (H.Space j.unop))
  have hy : y ∈ Set.range ((TopCat.limitCone.{1, 0} T).π.app (op a)) := by
    rw [D5.S1.Dynamics.Shadowing.compact_projection_image.{1, 0} T (op a)]
    apply (Functor.mem_eventualRange_iff _).2
    intro j f
    obtain ⟨x, hx⟩ := H.onto a j.unop (leOfHom f.unop) y
    exact ⟨x, Subtype.ext hx⟩
  obtain ⟨x, hx⟩ := hy
  let e := (H.coneIsLimit hl).conePointUniqueUpToIso (Profinite.limitConeIsLimit.{1, 0} H.diagram)
  refine ⟨e.inv x, ?_⟩
  have he := ConcreteCategory.congr_hom
    ((H.coneIsLimit hl).conePointUniqueUpToIso_inv_comp
      (Profinite.limitConeIsLimit.{1, 0} H.diagram) (op a)) x
  exact he.trans hx

/-- A compatible metric is chosen only for a proper countable stage. -/
@[instance_reducible]
noncomputable def properMetric (hc : l < ω₁) : MetricSpace H.LimitSpace := by
  letI : Countable (Coord l) := (Cardinal.countable_Iio_of_lt_omega_one hc).to_subtype
  exact TopologicalSpace.metrizableSpaceMetric H.LimitSpace

instance spaceMeasurable (a : Coord l) : MeasurableSpace (H.Space a) := borel (H.Space a)
instance spaceBorel (a : Coord l) : BorelSpace (H.Space a) := ⟨rfl⟩
instance limitMeasurable : MeasurableSpace H.LimitSpace := borel H.LimitSpace
instance limitBorel : BorelSpace H.LimitSpace := ⟨rfl⟩

end Prefix

/-- Regularity is explicit in the signed carrier. -/
def RegularSigned (K : Type*) [TopologicalSpace K] [MeasurableSpace K] :=
  {s : SignedMeasure K // Measure.Regular s.toJordanDecomposition.posPart ∧
    Measure.Regular s.toJordanDecomposition.negPart}

/-- The original one-sided cofinite inclusion. -/
abbrev AlmostSubset (A B : Set ℕ) := A ≤ᶠ[cofinite] B

/-- The filter in the original every-choice F clause. -/
def along (J : Set ℕ) : Filter ℕ := atTop ⊓ 𝓟 J

namespace Prefix

variable {l : Ordinal.{0}} (H : Prefix l)

/-- Bookkeeping is used only on its original eligible domains. Total functions
provide harmless values off those domains, without requiring any obligations there. -/
structure Data where
  proper : l < ω₁
  I : Coord l → Coord l → Set ℕ
  J : Coord l → Coord l → Coord l → Set ℕ
  N : Coord l → Coord l → Bool → Set ℕ
  V : (r : Coord l) → ℕ → Set (H.Space r)
  Vclopen : ∀ r n, IsClopen (V r n)
  nu : (r : Coord l) → Label → ℕ → RegularSigned (H.Space r)
  mass : ∀ r d n, ω ≤ r.1 → (nu r d n).1.totalVariation univ = 1

/-- Actual signed norm-preserving lifts; no positivity restriction is imposed. -/
def OldClass (D : H.Data) (r d a : Coord l) (h : r ≤ a) (n : ℕ)
    (s : RegularSigned (H.Space a)) : Prop :=
  s.1.totalVariation univ = 1 ∧ s.1.map (H.map r a h) = (D.nu r ⟨d.1, d.2.trans D.proper⟩ n).1

/-- The literal new lift class on the actual new coordinate space. -/
def NewClass (D : H.Data) (r d : Coord l) (n : ℕ)
    (s : RegularSigned H.LimitSpace) : Prop :=
  s.1.totalVariation univ = 1 ∧ s.1.map (H.projection r) = (D.nu r ⟨d.1, d.2.trans D.proper⟩ n).1

/-- All old obligations, with delayed labels and finite initial domains preserved. -/
structure Laws (D : H.Data) : Prop where
  A : ∀ r d a, ω ≤ r.1 → r < a → d < a → D.J r d a ⊆ D.I r a
  B : ∀ r d, ω ≤ r.1 → Disjoint (D.N r d false) (D.N r d true)
  C : ∀ r d a e, ω ≤ r.1 → r < a → d < a → (D.J r d a ∩ D.N r d e).Infinite
  DI : ∀ r a b, ω ≤ r.1 → r < a → a ≤ b → AlmostSubset (D.I r b) (D.I r a)
  DJ : ∀ r d a b, ω ≤ r.1 → r < a → d < a → a ≤ b →
    AlmostSubset (D.J r d b) (D.J r d a)
  E : ∀ r a (h : r < a) (xi : Coord a.1), ω ≤ r.1 → r.1 ≤ xi.1 →
    ∀ᶠ n in along (D.I r a), ∀ u v : H.Space a,
      H.map r a h.le u ∈ D.V r n → H.map r a h.le v ∈ D.V r n →
      H.map r a h.le u = H.map r a h.le v → u.1 xi = v.1 xi
  F : ∀ r d a (hr : r < a), ω ≤ r.1 → d < a →
    ∀ s : ℕ → RegularSigned (H.Space a),
      (∀ n, H.OldClass D r d a hr.le n (s n)) →
      ∃ mu : RegularSigned (H.Space a), mu.1.totalVariation.real univ ≤ 1 ∧
        Tendsto (fun n => (Measures.NormPreservingLifts.signedFunctional (s n).1).toWeakDual)
          (along (D.J r d a))
          (𝓝 (Measures.NormPreservingLifts.signedFunctional mu.1).toWeakDual)

/-- Complete new proper-stage obligations. The same N from D is used literally. -/
structure Extension (D : H.Data) where
  limit_isLimit : IsLimit H.cone
  onto : ∀ a, Function.Surjective (H.projection a)
  inhabited : Nonempty H.LimitSpace
  I : Coord l → Set ℕ
  J : Coord l → Coord l → Set ℕ
  A : ∀ r d, ω ≤ r.1 → J r d ⊆ I r
  B : ∀ r d, ω ≤ r.1 → Disjoint (D.N r d false) (D.N r d true)
  C : ∀ r d e, ω ≤ r.1 → (J r d ∩ D.N r d e).Infinite
  DI : ∀ r a, ω ≤ r.1 → r < a → AlmostSubset (I r) (D.I r a)
  DJ : ∀ r d a, ω ≤ r.1 → r < a → d < a → AlmostSubset (J r d) (D.J r d a)
  E : ∀ r (xi : Coord l), ω ≤ r.1 → r.1 ≤ xi.1 →
    ∀ᶠ n in along (I r), ∀ u v : H.LimitSpace,
      H.projection r u ∈ D.V r n → H.projection r v ∈ D.V r n →
      H.projection r u = H.projection r v → u.1 xi = v.1 xi
  nonvacuous : ∀ r d n, ω ≤ r.1 → ∃ s, H.NewClass D r d n s
  F : ∀ r d, ω ≤ r.1 → ∀ s : ℕ → RegularSigned H.LimitSpace,
    (∀ n, H.NewClass D r d n (s n)) →
    ∃ mu : RegularSigned H.LimitSpace, mu.1.totalVariation.real univ ≤ 1 ∧
      Tendsto (fun n => (Measures.NormPreservingLifts.signedFunctional (s n).1).toWeakDual)
        (along (J r d))
        (𝓝 (Measures.NormPreservingLifts.signedFunctional mu.1).toWeakDual)

end Prefix

/-- A cofinite inclusion restricts every old subsequence conclusion in its
original filter form. -/
private theorem along_le {A B : Set ℕ} (h : AlmostSubset A B) : along A ≤ along B := by
  apply le_inf inf_le_left
  rw [le_principal_iff]
  apply eventually_inf_principal.2
  exact h.filter_mono atTop_le_cofinite

private theorem choose_row_sets {l : Ordinal.{0}} (H : Prefix l)
    (hl : Order.IsSuccLimit l) (hc : l < ω₁) (D : H.Data) (L : H.Laws D)
    (r : Coord l) (hr : ω ≤ r.1) :
    ∃ I : Set ℕ, ∃ J : Coord l → Set ℕ,
      (∀ d, J d ⊆ I) ∧
      (∀ d e, (J d ∩ D.N r d e).Infinite) ∧
      (∀ a, r < a → AlmostSubset I (D.I r a)) ∧
      (∀ d a, r < a → d < a → AlmostSubset (J d) (D.J r d a)) := by
  classical
  letI : Countable (Coord l) := (Cardinal.countable_Iio_of_lt_omega_one hc).to_subtype
  letI : Encodable (Coord l) := Encodable.ofCountable (Coord l)
  let Upper := {a : Coord l // r < a}
  letI : Nonempty Upper := ⟨⟨⟨Order.succ r.1, hl.succ_lt r.2⟩, Order.lt_succ r.1⟩⟩
  obtain ⟨a', ha'mono, ha'top⟩ := exists_seq_monotone_tendsto_atTop_atTop Upper
  let a : ℕ → Coord l := fun j => (a' j).1
  have har (j : ℕ) : r < a j := (a' j).2
  have hamono : Monotone a := fun i j hij => ha'mono hij
  have habove (b : Coord l) : ∃ j, b < a j := by
    let c : Upper := ⟨⟨max (Order.succ r.1) (Order.succ b.1),
      max_lt (hl.succ_lt r.2) (hl.succ_lt b.2)⟩,
      (Order.lt_succ r.1).trans_le (le_max_left _ _)⟩
    obtain ⟨j, hj⟩ := eventually_atTop.1 ((tendsto_atTop.1 ha'top) c)
    exact ⟨j, (Order.lt_succ b.1).trans_le ((le_max_right _ _).trans (hj j le_rfl))⟩
  let label : ℕ → Coord l := fun k => (Encodable.decode k).getD r
  have hlabel (d : Coord l) : label (Encodable.encode d) = d := by
    simp [label, Encodable.encodek]
  let active : ℕ → ℕ → Prop := fun k j => k ≤ j ∧ label k < a j
  have hfinite (j : ℕ) : {k | active k j}.Finite :=
    (Set.finite_le_nat j).subset (fun k hk => hk.1)
  have heventual (k : ℕ) : ∃ j₀, ∀ j, j₀ ≤ j → active k j := by
    obtain ⟨j₀, hj₀⟩ := habove (label k)
    refine ⟨max k j₀, fun j hj => ⟨(le_max_left _ _).trans hj, ?_⟩⟩
    exact hj₀.trans_le (hamono ((le_max_right _ _).trans hj))
  obtain ⟨v, I, J, hv, hJdef, hIdef, hpool, hIold, hJold⟩ :=
    CountableJointFusion.exists_countable_joint_finite_block_fusion
      active hfinite heventual (fun j => D.I r (a j))
      (fun k j => D.J r (label k) (a j)) (fun k => D.N r (label k))
      (fun k j hkj => L.A r (label k) (a j) hr (har j) hkj.2)
      (fun {i j} hij => L.DI r (a i) (a j) hr (har i) (hamono hij))
      (fun k {i j} hki hkj hij =>
        L.DJ r (label k) (a i) (a j) hr (har i) hki.2 (hamono hij))
      (fun k j e hkj => L.C r (label k) (a j) e hr (har j) hkj.2)
  refine ⟨I, fun d => J (Encodable.encode d), ?_, ?_, ?_, ?_⟩
  · intro d n hn
    rw [hIdef]
    exact Set.mem_iUnion.2 ⟨Encodable.encode d, hn⟩
  · intro d e
    simpa only [hlabel] using hpool (Encodable.encode d) e
  · intro b hb
    obtain ⟨j, hj⟩ := habove b
    exact (hIold j).trans (L.DI r b (a j) hr hb hj.le)
  · intro d b hrb hdb
    obtain ⟨j, hj⟩ := habove b
    obtain ⟨j₀, hj₀⟩ := heventual (Encodable.encode d)
    let q := max j j₀
    have hq : active (Encodable.encode d) q := hj₀ q (le_max_right _ _)
    have hba : b ≤ a q := hj.le.trans (hamono (le_max_left _ _))
    have hfirst := hJold (Encodable.encode d) q hq
    rw [hlabel] at hfirst
    exact hfirst.trans (L.DJ r d b (a q) hr hrb hdb hba)

namespace Prefix

variable {l : Ordinal.{0}} (H : Prefix l)

/-- Proper-stage convergence is proved for the literal new space and every
all-Nat selection. No new convergence or clopen-descent premise is accepted. -/
theorem exists_joint_proper_limit_extension (hl : Order.IsSuccLimit l)
    (hc : l < ω₁) (hw : ω < l) (D : H.Data) (L : H.Laws D) :
    Nonempty (H.Extension D) := by
  classical
  letI : Nonempty (Coord l) := ⟨⟨ω, hw⟩⟩
  letI : MetricSpace H.LimitSpace := H.properMetric hc
  letI : CompactSpace H.LimitSpace := H.limitCompact
  letI : ∀ a : Coord l, Nonempty (H.Space a) := fun a => H.spaceNonempty a
  letI : Countable (Coord l) := (Cardinal.countable_Iio_of_lt_omega_one hc).to_subtype
  letI : ∀ a : Coord l, MetricSpace (H.Space a) := fun a => by
    letI : Countable (Coord a.1) :=
      (Cardinal.countable_Iio_of_lt_omega_one (a.2.trans hc)).to_subtype
    exact TopologicalSpace.metrizableSpaceMetric (H.Space a)
  letI : ∀ a : Coord l, CompactSpace (H.Space a) := fun a => H.spaceCompact a
  letI : ∀ a : Coord l, MeasurableSpace (H.Space a) := fun a => H.spaceMeasurable a
  letI : ∀ a : Coord l, BorelSpace (H.Space a) := fun a => H.spaceBorel a
  have hsets : ∀ r : Coord l, ω ≤ r.1 →
      ∃ I : Set ℕ, ∃ J : Coord l → Set ℕ,
        (∀ d, J d ⊆ I) ∧
        (∀ d e, (J d ∩ D.N r d e).Infinite) ∧
        (∀ a, r < a → AlmostSubset I (D.I r a)) ∧
        (∀ d a, r < a → d < a → AlmostSubset (J d) (D.J r d a)) :=
    fun r hr => choose_row_sets H hl hc D L r hr
  let I : Coord l → Set ℕ := fun r =>
    if hr : ω ≤ r.1 then (hsets r hr).choose else ∅
  let J : Coord l → Coord l → Set ℕ := fun r =>
    if hr : ω ≤ r.1 then (hsets r hr).choose_spec.choose else fun _ => ∅
  have hproperties (r : Coord l) (hr : ω ≤ r.1) :
      (∀ d, J r d ⊆ I r) ∧
      (∀ d e, (J r d ∩ D.N r d e).Infinite) ∧
      (∀ a, r < a → AlmostSubset (I r) (D.I r a)) ∧
      (∀ d a, r < a → d < a → AlmostSubset (J r d) (D.J r d a)) := by
    simpa only [I, J, dite_eq_left hr] using (hsets r hr).choose_spec.choose_spec
  refine ⟨{
    limit_isLimit := H.coneIsLimit hl
    onto := H.projection_surjective hl
    inhabited := by
      let a : Coord l := ⟨ω, hw⟩
      obtain ⟨y⟩ := (inferInstance : Nonempty (H.Space a))
      obtain ⟨x, hx⟩ := H.projection_surjective hl a y
      exact ⟨x⟩
    I := I
    J := J
    B := L.B
    A := fun r d hr => (hproperties r hr).1 d
    C := fun r d e hr => (hproperties r hr).2.1 d e
    DI := fun r a hr h => (hproperties r hr).2.2.1 a h
    DJ := fun r d a hr hra hda => (hproperties r hr).2.2.2 d a hra hda
    E := ?_
    nonvacuous := ?_
    F := ?_ }⟩
  · intro r xi hr hrxi
    let a : Coord l := ⟨Order.succ xi.1, hl.succ_lt xi.2⟩
    have hra : r < a := hrxi.trans_lt (Order.lt_succ xi.1)
    let xi' : Coord a.1 := ⟨xi.1, Order.lt_succ xi.1⟩
    have hE := L.E r a hra xi' hr hrxi
    have hE' := hE.filter_mono (along_le ((hproperties r hr).2.2.1 a hra))
    filter_upwards [hE'] with n hn u v hu hv huv
    have hru : H.map r a hra.le (H.projection a u) = H.projection r u := by
      ext i; rfl
    have hrv : H.map r a hra.le (H.projection a v) = H.projection r v := by
      ext i; rfl
    exact hn (H.projection a u) (H.projection a v)
      (hru.symm ▸ hu) (hrv.symm ▸ hv) (hru.trans (huv.trans hrv.symm))
  · intro r d n hr
    obtain ⟨s, hs, hmass⟩ := Measures.NormPreservingLiftExistence.exists_norm_preserving_lift
      (H.projection r) (H.projection r).continuous (H.projection_surjective hl r) (D.nu r ⟨d.1, d.2.trans D.proper⟩ n).1
    refine ⟨⟨s, inferInstance, inferInstance⟩, ?_⟩
    exact ⟨hmass.trans (D.mass r ⟨d.1, d.2.trans D.proper⟩ n hr), hs⟩
  · intro r d hr s hs
    have hJinf : (J r d).Infinite :=
      ((hproperties r hr).2.1 d false).mono Set.inter_subset_left
    let enum : ℕ → ℕ := Nat.nth (· ∈ J r d)
    have henumMono : StrictMono enum := Nat.nth_strictMono hJinf
    have henum : Tendsto enum atTop (along (J r d)) :=
      tendsto_inf.2 ⟨henumMono.tendsto_atTop,
        tendsto_principal.2 (Eventually.of_forall (Nat.nth_mem_of_infinite hJinf))⟩
    have hbound (n : ℕ) : (s (enum n)).1.totalVariation.real univ ≤ 1 := by
      simp only [Measure.real, (hs (enum n)).1, ENNReal.toReal_one, le_refl]
    have hclopen (A : Set H.LimitSpace) (hA : IsClopen A) :
        CauchySeq (fun n => (s (enum n)).1 A) := by
      obtain ⟨aop, U, hU, hAU⟩ :=
        Profinite.exists_isClopen_of_cofiltered.{0, 1} H.cone (H.coneIsLimit hl) hA
      let b : Coord l := ⟨max aop.unop.1 (max (Order.succ r.1) (Order.succ d.1)),
        max_lt aop.unop.2 (max_lt (hl.succ_lt r.2) (hl.succ_lt d.2))⟩
      have hab : aop.unop ≤ b := by
        change aop.unop.1 ≤ max aop.unop.1 _
        exact le_max_left _ _
      have hrb : r < b := (Order.lt_succ r.1).trans_le
        ((le_max_left _ _).trans (le_max_right _ _))
      have hdb : d < b := (Order.lt_succ d.1).trans_le
        ((le_max_right _ _).trans (le_max_right _ _))
      let W : Set (H.Space b) := H.map aop.unop b hab ⁻¹' U
      have hW : IsClopen W := hU.preimage (H.map _ _ _).continuous
      have hAW : A = H.projection b ⁻¹' W := by
        rw [hAU]
        rfl
      let t : ℕ → RegularSigned (H.Space b) := fun n =>
        ⟨(s n).1.map (H.projection b), inferInstance, inferInstance⟩
      have htbase (n : ℕ) :
          (t n).1.map (H.map r b hrb.le) = (D.nu r ⟨d.1, d.2.trans D.proper⟩ n).1 := by
        apply VectorMeasure.ext
        intro V hV
        rw [VectorMeasure.map_apply _ (H.map r b hrb.le).continuous.measurable hV,
          VectorMeasure.map_apply _ (H.projection b).continuous.measurable
            ((H.map r b hrb.le).continuous.measurable hV)]
        rw [← (hs n).2,
          VectorMeasure.map_apply _ (H.projection r).continuous.measurable hV]
        rfl
      have htmass (n : ℕ) : (t n).1.totalVariation univ = 1 := by
        apply le_antisymm
        · have h := VectorMeasure.variation_map_le (μ := (s n).1)
            (φ := H.projection b) univ
          simpa only [← SignedMeasure.totalVariation_eq_variation,
            Measure.map_apply (H.projection b).continuous.measurable MeasurableSet.univ,
            preimage_univ, (hs n).1] using h
        · have h := VectorMeasure.variation_map_le (μ := (t n).1)
            (φ := H.map r b hrb.le) univ
          simpa only [← SignedMeasure.totalVariation_eq_variation,
            htbase n, Measure.map_apply (H.map r b hrb.le).continuous.measurable MeasurableSet.univ,
            preimage_univ, D.mass r ⟨d.1, d.2.trans D.proper⟩ n hr] using h
      obtain ⟨mu, hmumass, hF⟩ := L.F r d b hrb hr hdb t
        (fun n => ⟨htmass n, htbase n⟩)
      have hF' := hF.mono_left
        (along_le ((hproperties r hr).2.2.2 d b hrb hdb))
      have hscalar := (tendsto_iff_forall_eval_tendsto_topDualPairing.mp hF')
        ((LocallyConstant.charFn ℝ hW).toContinuousMap)
      change Tendsto (fun n => Measures.NormPreservingLifts.signedFunctional (t n).1
          (LocallyConstant.charFn ℝ hW).toContinuousMap) (along (J r d))
        (𝓝 (Measures.NormPreservingLifts.signedFunctional mu.1
          (LocallyConstant.charFn ℝ hW).toContinuousMap)) at hscalar
      have heval (n : ℕ) :
          Measures.NormPreservingLifts.signedFunctional (t n).1
              (LocallyConstant.charFn ℝ hW).toContinuousMap = (s n).1 A := by
        rw [Measures.ClopenCauchyConvergence.signedFunctional_charFn (t n).1 hW,
          VectorMeasure.map_apply _ (H.projection b).continuous.measurable hW.isClosed.measurableSet,
          ← hAW]
      have hscalar' : Tendsto (fun n => (s n).1 A) (along (J r d))
          (𝓝 (mu.1 W)) := by
        simpa only [heval, Measures.ClopenCauchyConvergence.signedFunctional_charFn mu.1 hW]
          using hscalar
      exact (hscalar'.comp henum).cauchySeq
    obtain ⟨mu, hmu, hpos, hneg, hconv⟩ :=
      Measures.ClopenCauchyConvergence.tendsto_signedFunctional_of_clopen_cauchy
        1 (by norm_num) (fun n => (s (enum n)).1) hbound hclopen
    refine ⟨⟨mu, hpos, hneg⟩, hmu, ?_⟩
    apply tendsto_def.2
    intro U hU
    obtain ⟨k, hk⟩ := eventually_atTop.1 (hconv hU)
    apply eventually_inf_principal.2
    filter_upwards [eventually_ge_atTop (enum k)] with n hn hnJ
    have hnrange : n ∈ Set.range (Nat.nth (· ∈ J r d)) :=
      (Nat.range_nth_of_infinite hJinf).symm.subset hnJ
    obtain ⟨m, hm⟩ := hnrange
    rw [← hm] at hn ⊢
    exact hk m (henumMono.le_iff_le.mp hn)

end Prefix

end D5.S3.Topology.InverseLimit.SignedProperLimit
