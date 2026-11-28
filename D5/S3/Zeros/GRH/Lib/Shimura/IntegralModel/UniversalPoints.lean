/- GID: D5/S3/Zeros/GRH/Lib/Shimura/IntegralModel/UniversalPoints
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/IntegralModel/UniversalPoints
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.IntegralModel.UniversalPoints. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/IntegralModel/UniversalPoints.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Geometry.Lefschetz
import D5.S3.Zeros.GRH.Lib.Shimura.ThetaGroup.RigidFibres
import D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation.BallModel
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Integral Kuga–Sato models for GU(1,n−1) with level covers and congruence relation
(known result; see Lib.Shimura.IntegralModel.ModelExistence).

Part of: Eichler–Shimura congruence relation for GU(1,n−1) at a split place: the pointwise step
(known result; see Lib.Shimura.CongruenceRelation.CongruenceStep).

This file: Deep principal levels for finitely many isogenies; finite torsion index sets. Hecke
isogenies at a split place: multiplier, action on level points, kernel in w-torsion. Kuga–Sato fibre
powers, their complex points up to isomorphism, and level covers as closures. -/

noncomputable section

open NumberField Subgroup Submodule nonZeroDivisors
variable {E n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] {𝔑 : 𝓞 E} (𝔪 : (𝓞 E)⁰)

@[simp] lemma levelGU_inf_one : levelGU n 𝔑 ⊓ levelGU n 1 = levelGU n 𝔑 := inf_of_le_left fun _ h ↦
  mem_levelGU_of_local h.1 h.2.1 (·.2.one_notMem.elim)

/-- For 𝔑 ≠ 0 and a finite set s of pairs (𝔪, g), there is a level m with g⁻¹K(m)g ⊂ K(𝔑) ∩ K(𝔪)
for all (𝔪, g) in s and for (1, 1) and (m, 1). -/
lemma exists_level_conj_mem (h : 𝔑 ≠ 0) (s : Finset ((𝓞 E)⁰ × GUPlus E n)) : ∃ m,
  ∀ x ∈ insert (m, 1) (insert 1 s), ∀ k ∈ levelGU n m.1, x.2.1⁻¹ * k * x.2 ∈ levelGU n 𝔑 ⊓ levelGU n
  x.1 := have ⟨M, _, H⟩ := (exists_congruenceGL_subset ((insert 1 s).eventually_all.2 fun x _ ↦
    (by fun_prop : ContinuousAt (x.2.1⁻¹ * · * x.2) 1) (((isOpen_congruenceGL_span h).inter
    (isOpen_congruenceGL_span (coe_ne_zero x.1))).mem_nhds (by simp))))
  ⟨⟨M, by simpa⟩, by
    simp_all [levelGU]; rintro _ _ _ ⟨a, b⟩ s k c d
    simp [mul_mem, inv_mem, *, (H k d).2 _ _ _ _ s]⟩

/-- For a non-zero element 𝔪 of O_E, the set of non-zero elements of (𝔸_f / Ô)ⁿ ≅ (E / O_E)ⁿ
killed by 𝔪. -/
abbrev NonzeroTorsion n := {s : torsionBy _ (AdelicTorsion E n) 𝔪.1 // s ≠ 0}

instance finite_torsionBy :
  Finite (torsionBy _ (AdelicTorsion E n) 𝔪.1) := Nat.finite_of_card_ne_zero
  (by rw [← torsionBySet_span_singleton_eq, card_torsionBySet_adelicTorsion] <;> simp)

instance : ((levelGU n 𝔪).subgroupOf (levelGU n 𝔑)).FiniteIndex := ⟨relIndex_inf_ne_zero (by
  simp [relIndex_eq_one.2, levelGU]) ((isCompact_intGL isCompact_Ô).relIndex_ne_zero
  (isOpen_congruenceGL_span (by simp)) ∘ relIndex_eq_zero_of_le_right fun _ ↦ (·.2.1))⟩

open Matrix IsDedekindDomain HeightOneSpectrum Nat Set QuadField GeneralLinearGroup

attribute [-simp] coe_units_inv MonoidHom.coe_comp

section

variable {E n : Type} [Field E] [NumberField E] [Fintype n]

/-- The `w`-torsion of `(𝔸_f / Ô)ⁿ` is a copy of `(𝓞 / w)ⁿ`, and an integral matrix kills a
torsion point exactly when its reduction modulo `w` kills the corresponding vector. -/
lemma exists_residue_torsion_emb w : ∃ ρ : _ →ₗ[𝓞 E] _, (⇑ρ).Injective ∧ ρ.range = .torsionBySet _ _
  w.1 ∧ ∀ x, ∃ v, ρ x = torsionClass v ∧ ∀ g : Matrix n n (Ô E), torsionClass (g.map (·.1) *ᵥ
  v) = 0 ↔ x ∈ residueKer (g.map (·.1 w)) := have L (x : n → Ô E) : torsionClass (singleAdele w
    (uniformizer w).1⁻¹ • (·.1) ∘ x) = 0 ↔ reduceAt w ∘ x = 0 := by simp_all [funext_iff, mem_Ô,
    ← and_forall_ne w, ← v_uniformizer_inv_mul_le_one_iff]
  let p := (Algebra.linearMap (𝓞 E) (ResField w)).compLeft n
  have hk : (torsionClass ∘ₗ ((_ : 𝔸f E) • (Algebra.linearMap ..).compLeft n)).ker = p.ker :=
    Submodule.ext (L <| algebraMap .. ∘ ·)
  have hp : (⇑p).Surjective := (algebraMap_ResField_surjective w).comp_left
  let ρ := liftQ _ _ hk.ge ∘ₗ (p.quotKerEquivOfSurjective hp).symm.1
  have I := ρ.ker_eq_bot.1 (by simp [ρ, LinearMap.ker_comp, ker_liftQ, *])
  by use ρ, I, SetLike.ext' (Finite.eq_of_subset_of_card_le (finite_of_card_ne_zero ?_)
    (by simp_all [subset_def, ← map_smul, funext_iff, Algebra.smul_def])
    (card_range_of_injective I ▸ ?_)), hp.forall.2 fun c ↦ ⟨_, by aesop, fun g ↦ by
    simpa [residueOrZero, funext_iff, mulVec_apply_eq_sum, mem_Ô.1] using! L (g *ᵥ algebraMap .. ∘
      c)⟩ <;> erw [card_torsionBySet_adelicTorsion w.3] <;> simp [card_pi, card_ResField]

end

variable {E n : Type} [Field E] [CMBase E] [Fintype n] {D : PEL E} {d₀ : ℕ} [HasQuadSubfield d₀ E]
  {v : n → 𝔸f E} {w : SplitFinPlace E} {C : Submodule (ResField w.1) (n → ResField w.1)}

omit [Fintype n] in
lemma smul_torsionClass_eq_zero_iff {a} : a • torsionClass v = 0 ↔ ∀ i u,
  u.intValuation a * Valued.v (v i u) ≤ 1 :=
  torsionClass_eq_zero.trans (by simp [mem_Ô, ← v_algebraMap_eq_intValuation, ← map_mul]; rfl)

lemma heckeIsogeny_inv_at_eq_basicCosetRep {I} (hw : IsSafe I w.1) : (heckeIsogeny w C)⁻¹.1.map
  (evalAt _) = (basicCosetRep C).1 := by simp [↓← val_map_apply, heckeIsogeny,
  evalAt_centralScalar_of_ne hw.1.star_ne_and_prime_norm.1.symm, invTransposeGL, transposeGL]

lemma heckeIsogeny_inv_mulVec_of_ne {u} (hu : u ≠ w.1) (hu' :
  u.below _ ≠ star (w.1.below (QuadField d₀))) i : ((heckeIsogeny w C)⁻¹.1
  *ᵥ v) i u = v i u := ((evalAt u).map_mulVec ..).trans (by simp [↓← val_map_apply, heckeIsogeny,
  evalAt_centralScalar_of_ne hu', evalAt_conjAtSplit_of_ne _ hu (by grind [below_star, star_star])])

lemma isScalarFrame_heckeIsogeny : IsScalarFrame (heckeIsogeny w C)
  (w.1.q ^ Module.finrank (ResField w.1) C : ℕ) := ((centralScalar_mem_GU _).2 _ (by simp
  [finIdeleAbs_adeleNorm, norm_locField_eq_q_zpow])).imp_right
  (congr(IsFrameFor $(one_smul ..) _).mp <| ·.mul_iff.2 ⟨1, by simp⟩)

lemma heckeIsogeny_torsionClass C v (hβ : D.β = algebraMap _ _ (c₀ d₀)) (hw :
  IsSafe D.𝔑 w) {b : ℤ} (co : IsCoprime (D.β - b) (star D.β - b)) (hb : D.β - b ∈
  w.1.1) : let s := torsionClass ((heckeIsogeny w C)⁻¹.1 *ᵥ v); (torsionClass v ∈ D.levelTorsion →
    s = torsionClass v) ∧ ∀ N, (D.β - b) ^ N • torsionClass v = 0 → s = 0 →
    torsionClass v ∈ torsionBySet (𝓞 E) _ w.1.1 := by
  simp [PEL.levelTorsion, smul_torsionClass_eq_zero_iff, mem_Ô, torsionClass_eq_iff]
  use fun hv i u ↦ if e : D.𝔑 ∈ u.1 then by simp [heckeIsogeny_inv_mulVec_of_ne (by grind [IsSafe])
    (hw.2.2 u · e)] else have H i := by simpa [intValuation_eq_one_iff.2 e] using! hv i u
    ((LocInt u).1.comap (evalAt u)).sub_mem (sum_mem fun a _ ↦
      mul_mem (mem_Ô.1 ((heckeIsogeny_mem_GUPlus ..).2 i a)
    u) (H a)) (H i), fun N hv h a ha i u ↦ if hu : u = w then hu ▸ mul_le_mul'
    ((intValuation_le_pow_iff_mem _ _ 1).2 (by simpa)) ((congrArg _ (by simp [RingHom.map_mulVec,
    heckeIsogeny_inv_at_eq_basicCosetRep hw] : _ = (_ *ᵥ fun _ ↦ evalAt _ _) i)).trans_le
    (v_matrix_mul_le (basicCosetRep_spec C).1.2.1 (fun _ ↦ h · w) i i)) else mul_le_one'
    (intValuation_le_one ..) (if e : D.β - b ∈ _ then heckeIsogeny_inv_mulVec_of_ne hu (fun h ↦
    w.1.2.notMem_of_isCoprime_of_mem co hb (cast (by simpa [hβ, ↓D.star_beta] using! congr(c₀ _ -
    b ∈ ($h).1)) e)) i ▸ h .. else by simpa [intValuation_eq_one_iff.2 e] using hv i u)

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory ThetaFamily
  ThetaObject Obj Over Fintype TorusModel ValuativeArc ModuliPoint Fint Function
variable {E : Type} [Field E] [CMBase E] (D : PEL E)
  (R : Subalgebra (𝓞 E) E) {κ} {ν : ℕ} [Finite κ] {T : AlgebraicGeometry.Scheme}
  {Z : AlgebraicGeometry.Scheme}
  {τ : Z ⟶ AlgebraicGeometry.Spec (CommRingCat.of (NumberField.RingOfIntegers E))}
  {X : ThetaFamily D Z τ} {O : Type} [CommRing O] [ValuativeArc O]

/-- A universal family for D over a Dedekind ring R ⊂ E: projective smooth base of relative
dimension |n| − 1, with complex objects modelling all analytic families holomorphically,
dense in the base. -/
structure UniversalFamily where
  isDedekindDomain : IsDedekindDomain R
  base : Over (Spec ⟨R⟩)
  family : ThetaFamily D _ (base.hom ≫ specMap (algebraMap ..))
  hasProjEmbedding : HasProjEmbedding base.hom
  smooth : SmoothOfRelativeDimension (card D.Index - 1) base.hom
  obj : AnalyticFamily D × _ → (specOver R ℂ ⟶ base)
  model a : TorusModel (X := family) (obj a).left (a.1.torus a.2).toPeriodMap
  holomorphic f : ∀ b ∈ f.U, ∀ z, HolomorphicAt (fun q ↦
    atGeneric (model (f, q.1)).uniformisation.expMap q.2 ≫ (toFamily (obj _).left).left) (b, z)
  dense : IsDenseFamily (obj · |>.left)

attribute [instance] UniversalFamily.hasProjEmbedding

variable {D R} {U : UniversalFamily D R} (𝔪 : (𝓞 E)⁰) (y : ThetaObject X T) (Q : κ →
  (𝟙_ _ ⟶ y.groupScheme))

instance {S : Scheme} {F : Discrete κ ⥤ Over S} : HasLimit F := inferInstance

/-- For a family X and a finite index type κ, the fibre power over the base of X of κ copies of
its abelian scheme. -/
abbrev ThetaFamily.fibrePower κ [Finite.{1} κ] := ∏ᶜ fun _ : κ ↦ X.A

/-- The i-th projection from the fibre power `ThetaFamily.fibrePower` of the family X to its abelian
scheme, as a morphism of the underlying schemes. -/
abbrev ThetaFamily.proj i := (Pi.π _ i : X.fibrePower κ ⟶ _).left

/-- The T-point of the fibre power `ThetaFamily.fibrePower` lying over the object y whose i-th
component is the section Q_i of the abelian scheme of y. -/
def ThetaObject.pointOf : T ⟶ (X.fibrePower κ).left :=
  (Pi.lift (y.isGroupBaseChange.pointEquiv <| Q ·)).left

variable {y Q} (a : ModuliPoint E D.Index ν) (t :
  Spec ⟨O⟩ ⟶ (X.fibrePower (NonzeroTorsion 𝔪 D.Index ⊕ Fin ν)).left)

/-- t is `ThetaObject.pointOf` of an object modelled on the frame and line of a, with sections the
images of the non-zero 𝔪-torsion classes and of the P_i under the model. -/
@[mk_iff] inductive ThetaFamily.IsPointOf : Prop | mk {x V} [FinComplexSpace V] {Y :
  PeriodMap D a.x a.reflection V} (m : TorusModel x Y)
  (h : t = x.pointOf ((m.fullStructure.torsionPoint ·.1) ⊕ᵥ (m.π <| a.P ·)))

@[reassoc (attr := simp)] lemma ThetaObject.pointOf_hom : y.pointOf Q ≫ hom _ =
  y := by simp [pointOf]

@[reassoc (attr := simp)] lemma ThetaObject.pointOf_proj i : y.pointOf Q ≫ proj i =
  (Q i).left ≫ y.toFamily.left := congrArg Hom.left (Pi.lift_comp_π ..)

/-- For a = (x, ℓ, P), a chosen complex point over R of the fibre power of the family: an object
modelled on (x, ℓ), with its non-zero 𝔪-torsion points and the points P. -/
def UniversalFamily.datumPoint := ((exists_ball_family a).elim fun f h ↦ h.2.1 ▸ ⟨homMk _, U.model
  (f, 0), rfl⟩ : ∃ t : specOver R ℂ ⟶ (Over.map U.base.hom) _, U.family.IsPointOf 𝔪 a t.1).choose

lemma fibrePower_ext_iff {t t' : T ⟶ _} : t = t' ↔ t ≫ (X.fibrePower κ).hom = t' ≫ hom _ ∧ ∀ i, t ≫
  proj i = t' ≫ proj i := ⟨by lia, (congr($(show homMk (U := .mk _) t ·.1 = homMk t' by aesop).1))⟩

variable {𝔪} {a} {b : ModuliPoint E D.Index ν} {t} {J : Type} [Finite J]
  (γ : J → (𝓞 E)⁰ × GUPlus E D.Index) {s u : Spec ⟨ℂ⟩ ⟶ _}

attribute [local simp] act isLevelIso_iff fibrePower_ext_iff

/-- If the generic point of an O-point t of the fibre power, O an arc, is attached to a with its
𝔪-torsion (`ThetaFamily.IsPointOf`), then so is t. -/
lemma ThetaFamily.IsPointOf.of_generic (k : IsPointOf 𝔪 a (genericPt ≫ t)) : IsPointOf 𝔪 a t :=
  k.rec fun m h ↦ have H : IsPullbackAlong .. := ((reassoc_of% h) _).trans pointOf_hom
  (m.exists_model_over_arc H).elim fun m' E ↦ ⟨m', ext_of_isDominant_of_isSeparated (hom _)
    (by simp) genericPt (by simp [*, reassoc_of% E, H.comp_toFamily, fullStructure, ← π.eq_1])⟩

/-- Let s, u be complex points of a fibre power of the family X, attached (`ThetaFamily.IsPointOf`)
to a and b with their 𝔪-torsion. Then s = u iff some z is an isomorphism from a to b
(`ModuliPoint.IsLevelIso`) at level K(𝔑) ∩ K(𝔪). -/
lemma ThetaFamily.IsPointOf.eq_iff (h : X.IsPointOf 𝔪 a s) (k : IsPointOf 𝔪 b u) :
    s = u ↔ ∃ z, a.IsLevelIso (levelGU _ D.𝔑 ⊓ levelGU _ 𝔪) z b := by
  obtain ⟨⟨m, rfl⟩, m', rfl⟩ := h, k
  have J :=
    (Over.forget _).map_injective.comp ((isGroupBaseChange ‹_›).pointEquiv (T := 𝟙_ _)).injective
  simp [show ∀ w, w ∈ frameLattice b.x ↔ ‹PeriodMap ..›.Q w ∈ m'.uniformisation.L by
    simp [m'.lattice_eq, mem_classLattice, frameLattice], ← π.eq_1]
  use fun ⟨rfl, s, P⟩ ↦ ?_, fun ⟨z, ⟨h, k⟩, hz, P⟩ ↦ (m.exists_isogeny z hz m' rfl h.2.1.isIntMatrix
    (levelGU.isScalarFrame_inv_one h)).elim fun ρ ⟨ψ, _, _, c, v, p⟩ ↦ by
    suffices T : ∀ {𝔞}, _ ∈ levelGU D.Index 𝔞 → ∀ s ∈ torsionBy _ _ 𝔞,
      m.fullStructure.torsionPoint s ≫ ψ = m'.fullStructure.torsionPoint s from ((m.isRigid_pullback
      (.id _) (by simp [specMap])).eq_of_hom (Category.id_comp _) ρ.symm ψ (by simp [← pairing_comp,
      c]) (by rw [FullStructure.eta_eq, FullStructure.eta_eq, T h _ ·.2])).imp_right
      (by simp_all [← ·, ← comp_left_assoc, T k])
    rintro 𝔞 k ⟨y⟩ a; choose M m e using (mem_span_singleton_iff_exists_mul.1 <| k.2.2 · ·)
    erw [v, eq_add_of_sub_eq (Matrix.ext e : _ = 𝔞 • M), add_mulVec, smul_mulVec, ← mulVec_smul,
      map_add, torsionClass_mulVec_eq_zero m a]; aesop
  choose z hF hQ hz using m.exists_matrix_of_hom m' (𝟙 _) (hψ := ⟨by simp⟩) one_ne_zero (by simp)
  have T := m.torsionPoint_comp _ hF
  set k := _ * a.x
  simp at T
  have I {k} (h : ∀ {y}, _ = 0 → torsionClass (k *ᵥ y) = 0) (i j : D.Index) : k i j ∈ Ô E :=
    mul_one k ▸ torsionClass_eq_zero.1 (h (torsionClass_eq_zero.2 ((Ô E).matrix.one_mem · j))) i
  have K {𝔞} h (s : ∀ {y}, 𝔞 • y = 0 → m.fullStructure.torsionPoint y = _) : k ∈ levelGU _ 𝔞 :=
    ⟨⟨1, by
    simp [k, ↓← ‹PeriodMap ..›.isFrameFor.mul_iff, mul_assoc, ← IsFrameFor.conj_iff]
    convert ← ‹PeriodMap _ a.x ..›.isFrameFor
    ext; exact sub_eq_zero.1 ((traceForm_nondegenerate ℚ E).1 _ fun a ↦ by
      simpa [show D.ξ ≠ 0 from (by simpa [·] using D.xi_im_pos_and_re_eq_zero v₀), mul_assoc,
        mul_comm a] using hQ (toRealVectors (Pi.single _ a)) (toRealVectors (Pi.single _
        (star D.ξ⁻¹))))⟩, mem_intGL.2 ⟨I (m'.fullStructure.injective <| by simp [← T, ·]),
    I (m.fullStructure.injective <| by simp [T, ·])⟩, fun i j ↦
    mem_span_singleton_iff_exists_mul.2 ⟨_, torsionClass_eq_iff.1 (m'.fullStructure.injective
    (T (Pi.single j (isUnit_algebraMap_finAdele (a := 𝔞) h).unit⁻¹.1) ▸ s (torsionClass_eq_zero.2
    (by simp [ite_mem, Algebra.smul_def])))) i, by simp [mul_sub, mul_left_comm]⟩⟩
  use z, ⟨K D.level_ne_zero (m.fullStructure.eta_eq ⟨_, ·⟩ ▸ m'.fullStructure.eta_eq _),
    K (by simp) (dite _ (by simp [·]) <| (J ·) ∘ s _ ·)⟩, hz, (J <| hF _ ▸ P ·)

namespace UniversalFamily

/-- For a finite family γ of pairs (𝔪_j, g_j), the reduced closure, in a product of fibre
powers, of the tuples of complex points of a·(g_j, 1) with their 𝔪_j-torsion. -/
abbrev GraphClosure ν := ReducedClosure fun j a ↦ U.datumPoint (ν := ν) (γ j).1 (.act a (γ j).2)

variable {γ} (C : U.GraphClosure γ ν)

lemma isPointOf_datumPoint : U.family.IsPointOf 𝔪 a (datumPoint 𝔪 a).1 := by grind [datumPoint]

lemma IsPt.eq_datumPoint (h : U.family.IsPointOf 𝔪 a u) : u = (datumPoint 𝔪 a).1 :=
  (h.eq_iff isPointOf_datumPoint).2 ⟨1, by simp [ratConj]⟩

lemma datumPoint_eq_iff : U.datumPoint 𝔪 a = datumPoint 𝔪 b ↔ ∃ z, a.IsLevelIso (levelGU _ D.𝔑 ⊓
  levelGU _ 𝔪) z b := OverMorphism.ext_iff.trans (isPointOf_datumPoint.eq_iff isPointOf_datumPoint)

instance : HasProjEmbedding X.A.hom := ⟨X.embeds⟩

instance : HasProjEmbedding (X.fibrePower κ).hom := .pi (𝟙 _)

instance : HasProjEmbedding C.W.hom := .pi C.incl

lemma GraphClosure.exists_level_point_eq : ∃ m : (𝓞 E)⁰, ∀ {a b z}, IsLevelIso (levelGU _ m) z a b →
  C.point a = C.point b := (exists_level_conj_mem D.level_ne_zero (.image γ .univ)).imp fun _ h _ _
  z r ↦ C.hom_ext fun j ↦ by simpa [datumPoint_eq_iff, -act] using
  ⟨z, by simpa [mul_assoc] using h _ (by simp) _ r.mem_level, r.reflection_eq,
  (by simpa using realVecAction_mem_frameLattice (A := 1) (by simpa using (γ j).2.2.2) <|
  r.sub_mem_lattice ·)⟩

/-- The ν-fold fibre power Z of the universal family is smooth over R of relative dimension |n|
− 1 + ν|n|[E⁺:ℚ]; its complex points [a] (`UniversalFamily.datumPoint`, 𝔪 = 1) are dense, and
R-endomorphisms m_α of Z send [a·(g,1)] to [a·(g,α)]. -/
lemma fibrePower_spec ν : let Z := (Over.map U.base.hom) (fibrePower (_ ⊕ Fin ν))
  let c : _ → (_ ⟶ Z) := datumPoint 1; SmoothOfRelativeDimension (card D.Index - 1 + ν * abelianDim
    E D.Index) Z.hom ∧ IsDenseFamily (c · |>.1) ∧ ∃ m : _ → _, ∀ g α a, c (.act a g) ≫ m α =
    c (a.act g α) := suffices _ from ⟨Nat.add_comm .. ▸ smoothOfRelativeDimension_comp (hf := this)
    (hg := U.smooth) .., U.dense.of_fibres _ (s := this.smooth) fun a y h ↦ ⟨a.1.ballPoint 0 (_,
    fun i ↦ surjInv (U.model a).uniformisation.surjective ((ThetaObject.isGroupBaseChange
    _).pointEquiv.2 (homMk (y ≫ U.family.proj (.inr i))))), (IsPt.eq_datumPoint ⟨U.model a,
    fibrePower_ext_iff.2 (by simp_all [π, IsGroupBaseChange.pointEquiv, surjInv_eq])⟩).symm⟩,
    fun α ↦ (Over.map _).map (Limits.Pi.map (·.swap.elim α 1 • 𝟙 _)), fun g α a ↦
    isPointOf_datumPoint.rec fun m h ↦ by ext; exact IsPt.eq_datumPoint ⟨by exact m,
    (h =≫ _).trans (congrArg Hom.left (Pi.hom_ext (_ ≫ _) _ (by simp [π, m.equivariant])))⟩⟩
  Exists.elim (by refine ν.rec ⟨⟨Fan.mk (𝟙_ _) nofun, .mk (toUnit ·.1)⟩, ?_⟩ fun m ⟨F, H⟩ ↦
    ⟨⟨_, extendFanIsLimit _ F.2 (tensorProductIsBinaryProduct ..)⟩, ?_⟩ <;> simp [extendFan,
    add_mul, pullback.condition, add_comm] <;> infer_instance) fun F ↦
  (smoothOfRelativeDimension_isStableUnderBaseChange _).1 (.of_horiz_isIso ⟨(Pi.reindex
  (@Equiv.emptySum _ _ ⟨by simp⟩) (fun _ ↦ U.family.A) ≪≫ limit.isoLimitCone F).hom.3⟩)
