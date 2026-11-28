/- GID: D5/S3/Zeros/GRH/Lib/Weil/Periods/BesselIntegral
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Periods/BesselIntegral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Periods.BesselIntegral. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Periods/BesselIntegral.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.Periods.DegreeOfT
import D5.S3.Zeros.GRH.Lib.Weil.CompactLift.BranchingPeriod
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Transfer of Bessel and Fourier–Jacobi periods under a theta lift (one unfolding step)
(known result; see Lib.Weil.Periods.UnfoldingStep).

Part of: Reduction theory: Mahler-Godement compactness, finite covolume, adelic Minkowski theorems
(known result; see Lib.Adelic.Reduction.Defs).

This file: Heisenberg cocycle and translations on Hom in rational coordinates; kernels and
theta-lift predicate. Eichler maps; integral over the Bessel quotient reduced to the definite
unitary quotient. -/

open MatMul Space Matrix MeasureTheory Measure Subgroup Fintype
variable {E ι ι' : Type} [Field E] [CMType E] [Fintype ι] [Fintype ι'] {ε ε'} {V : Space E ι ε}
  {V' : Space E ι' ε'} [A : WeilData E] (x y) (a : ∀ n [Fintype n], AutChar E)

/-- The additive map y ↦ x'⁻¹ y x, taking an adelic matrix V → V' in rational coordinates to its
coordinates in the adelic frame of Hom(V, V'). -/
noncomputable def Space.homAtPoint (V : Space E ι ε) (V' : Space E _ ε') := show Matrix ι' ι
  (𝔸 E) →+ _ from .mk' (matToVec <| V'.x⁻¹.1 * · * V.x.1) (by simp)

variable (V V') in
/-- The Heisenberg bicharacter β of Hom(V, V') evaluated at two adelic matrices x, y given in
rational coordinates. -/
noncomputable abbrev Space.homBicharacter :=
  (adelicHeis E (homSigns ε ε')).β (V.homAtPoint V' x) (V.homAtPoint V' y)

/-- The representation `pairWeil` of U(V) × U(V′) on 𝒮(Hom(V, V′)) with twist (a ι)(det h)·(a
ι′)(det g)⁻¹, where ι, ι′ index the bases of V, V′. -/
noncomputable abbrev Space.twistedPairWeil := pairWeil V V' (a ι) (a ι')

lemma Space.homBicharacter_eq : V.homBicharacter V' x y = stdAddChar E
  (toAdele (A.j / 2) * (V.formAdjoint V' y * x).trace) := by simp [homBicharacter, adelicHeis,
  homAtPoint, kronecker_mulVec_eq_matToVec, formAdjoint, map_J_inv, map_J, V.x.1.trace_mul_cycle']

lemma Space.finCoord_homAtPoint : finCoord (V.homAtPoint V' x) =
  matToVec (A.α⁻¹.1 • (V'.xFin⁻¹.1 * x.map Prod.snd * V.xFin.1)) :=
  funext (by simp [homAtPoint, matToVec, xFin, Matrix.mul_apply, Prod.snd_sum, ← map_inv])

/-- The Heisenberg operator ϱ on 𝒮(Hom(V, V′)) at the frame coordinates `Space.homAtPoint` of an
adelic matrix x : V → V′ given in rational coordinates. -/
noncomputable abbrev Space.homHeisOp := (V.hom V').ϱ (V.homAtPoint V' x)

/-- The k o are theta lifts for the characters a o: for every polynomial P and functional t, some t′
satisfies ∫ θ(`twistedPairWeil` (a o) (g, h)(v_P ⊗ Φ))·t(g_∞⁻¹φ(g_f)) dg = t′(h_∞⁻¹(k o Φ φ)(h_f))
for all o, Φ, φ, h. -/
def Space.IsThetaLift {O : Type*} κ e e' (a : O → _) (k : O → ((stdSpace E ι).hom
  (stdSpace E ι')).finitePart →ₗ[ℂ] AlgForm (E := E) ι κ e →ₗ[ℂ] AlgForm ι' κ e') := ∀ P t, ∃ t',
  ∀ o Φ φ h, ∫ g, θ _ (twistedPairWeil (a o) (g, h) (integrated _ (polyVector _ P) Φ.1)) *
  algFormCoeff 1 t φ g ∂(stdSpace ..).quotMeasure = algFormCoeff 1 t' (k o Φ φ) h

namespace Grading

variable {E ι X : Type} [Field E] [CMType E] [Fintype ι] [Fintype X] {s} {ε : _} {N} {V : Space E ι
  ε} (Y : Grading V N X s)

attribute [-instance] IsAddTorsionFree.of_isDomain_charZero instCharZeroOfIsSemireal

attribute [local simp] HasDegreeGe mul_assoc eichlerMap

/-- The rational points are cocompact in the adelic Bessel subgroup B of Y: there is a compact C
⊆ B such that every g ∈ B has a rational γ ∈ B with γg ∈ C. -/
lemma isCocompact_ratBessel : (Y.ratBessel.subgroupOf Y.besselGroup).Cocpt := by
  choose A hA q hq using by simpa [ratAdeles, AddSubgroup.Cocpt, -Prod.forall] using
    IsCovolOneLattice.exists_compact_cover (ratAdeles E)
  choose D hD δ hδ hd using (stdSpace E X).exists_isCompact_of_definite
  obtain ⟨⟨p, _, u, x⟩, _, K, H⟩ := Y.exists_besselGroup_proj, V.exists_isCompact_of_bounded_frame
    ((hA.insert 1).insert 0).matrix (unitriangular (-Y.gradeOf ·) E)
  refine ⟨_, (K.mul (hD.image_auto Y.inclX)).preimage_val, fun g ↦ ?_⟩
  have s := Y.inclX_mem_ratBessel (hδ (p g))
  have hn := Y.mem_unipotent.1 (inv_mem (u (⟨_, s.2⟩ * g))); set n := V.ratCoordMatrix _
  have a i k := WellFounded.fix_eq (@Finite.to_wellFoundedLT _ _ (.lift Y.gradeOf)) (fun i γ ↦
    ite (-Y.gradeOf k ≤ -Y.gradeOf i) (diagonal 1 i k) (q (∑ l,
    (n - 1) i l * dite (Y.gradeOf l < _) ((↑) ∘ γ l) fun _ ↦ 0))) i
  have t i k h := a i k ▸ ite_eq_left h
  have ⟨x, e⟩ := (isUnit_iff_isUnit_det _).2 (det_eq_one_of_unitriangular t ▸ isUnit_one)
  have ⟨β, b, c⟩ := H _ ⟨x, mem_agreeWithOneOn.2 (e ▸ t)⟩ (fun i ↦ by
    clear_value n; clear * - a hn hq e; simp at hn
    simp +contextual [↓← congrFun₂ e, ite_eq_left_iff.2, sub_mul, mul_apply, *, -e] at a ⊢
    grind [sum_eq_single i] : n * _ ∈ _)
  have m := Y.ratBessel.mul_mem ⟨⟨β, rfl⟩, by clear * - c; simp_all [mem_besselGroup_iff, ratEmbed,
    U.map, ratCoordMatrix]⟩ s
  exact ⟨⟨_, m.2⟩, m, _, b, _, ⟨_, hd (p g), rfl⟩, by simp [*]⟩

attribute [local grind] gradeOf_stringReversal gradeOf_inl Finset.sum_eq_zero

/-- Let the adelic vector x lie in grades > max(0, k) and y in grade −k. Then the Eichler map of
x, y and ½h(y,y) is the matrix in rational coordinates of some u in the unipotent group
`Grading.unipotent`. -/
lemma exists_eichlerMap x y k (h : ∀ p, Y.gradeOf p ≤ 0 ⊔ k → x p = 0 := by grind) (h' : ∀ q,
  Y.gradeOf q ≠ -k → y q = 0 := by grind) : let J := V.J.map (↑); ∃ u ∈ Y.unipotent,
    V.ratCoordMatrix u = eichlerMap J x y
  (toAdele 2⁻¹ * star y ⬝ᵥ J *ᵥ y) := have H := V.isHermitian_J.map _ (star_toAdele · |>.symm)
  by refine ((reindex_equiv V.toRatCoords).2.1.1 (_root_.exists_unitary_eq_eichlerMap
    H ?_ ?_ ?_)).imp fun u f ↦ ⟨?_, f⟩ <;> simp [↓star_mul, ↓star_form H, *,
    dotProduct, ↓dotProduct_mulVec, Y.vecMul_J_apply, vecMulVec] <;> grind [star_zero]

/-- The measure on the Bessel (Fourier–Jacobi) subgroup B of Y that computes integrals over the
quotient of B by its rational points: Haar measure times a chosen cutoff. -/
noncomputable abbrev besselMeasure := (Y.ratBessel.subgroupOf Y.besselGroup).qms haar

instance isFiniteMeasure_besselMeasure : IsFiniteMeasure Y.besselMeasure :=
  isFiniteMeasure_quotMeasure_of_cocompact _ Y.isCocompact_ratBessel

instance : @IsMulRightInvariant Y.besselGroup _ _ haar :=
  isMulRightInvariant_of_finite_covolume Y.isFiniteMeasure_besselMeasure

/-- For distinct grade 1 indices v, one κ gives ∫_{[B]} φ = κ∫_{[U(X)]} M whenever φ is
continuous on U(V)(𝔸), left invariant under rational points of B, and φ(na) = f_a(c·(n −
1)_{v,X}) for unipotent n, f_a continuous periodic of mean M(a), M continuous on [U(X)]. -/
lemma integral_besselMeasure_eq_of_mean {q} [Fintype q] (v : q ↪ {l // Y.gradeOf l = 1}) :
  let row n (p : q × X) := Y.c * (V.ratCoordMatrix n - 1) (v p.1) (Y.indexEquiv (.inl p.2))
  ∃ κ, ∀ {φ} {f : _ → _ → ℂ} {M}, Y.ratBessel.FixesLeft φ → Continuous φ → (∀ᵉ (n ∈ Y.unipotent)
    (a), φ (n * Y.inclX a) = f a (row n)) → (∀ a, IsContPeriodic (_root_.ratVectors ..) (f a) ∧
    quotMean (_root_.ratVectors ..) (f a) = M a) → Continuous M → (stdSpace ..).Γ.FixesLeft M → ∫ r,
    φ r ∂Y.besselMeasure = κ * ∫ a, M a ∂(stdSpace ..).quotMeasure := by
  intro row
  obtain ⟨⟨p, hp, hu, hX, h1', hΓ⟩, C⟩ := Y.exists_besselGroup_proj, Y.isCocompact_ratBessel
  choose u v' e using fun b : q × X → _ ↦ Y.exists_eichlerMap (Pi.single 1 1 ∘ Y.gradeOf) (fun l ↦
    ∑ k, ite (l = Y.indexEquiv (.inl k.2)) ↑Y.c.1⁻¹ 0 * star (b k)) 0
  have := V.isEmbedding_ratCoordMatrix.continuous_iff.2
    ((continuous_congr e).2 (by fun_prop [eichlerMap]))
  have w (n : Y.unipotent) b : row (n * u b) = b + row n := funext fun k ↦ by
    have := (Y.mem_unipotent.1 n.2).mul (Y.mem_unipotent.1 (v' b)) le_rfl
    suffices row (u b) k = b k by simp [row, mul_sub, sub_mul] at *; grind
    have := @v.2.subsingleton _ _ _ ⟨by simp [reindex_equiv Y.indexEquiv]; omega⟩
    simp [row, e, (v _).2, vecMulVec_apply, Y.vecMul_J_apply, stringReversal, gradedGram,
      ← mul_assoc, Y.c.2, sum_prod_type, sum_subsingleton _ k.1, ← map_mul]
  have o : IsClosed ((stdSpace ..).Γ.comap p).carrier := isClosed_of_discreteTopology.preimage hp
  refine (exists_integral_quotMeasure_push _ _ _ hp (⟨_, hX ·⟩) hΓ).imp' _ fun κ H φ f M hi hc k fp
    l l' ↦ .trans (sub_eq_zero.1 ((integral_sub ?_ ?_).symm.trans
    (integral_quotMeasure_eq_zero_of_mean _ ?_ ?_ (mem_comap.2 ∘ hΓ ·) (_root_.ratVectors ..).qms
    (fun r b ↦ ⟨⟨_, Y.unipotent_le_besselGroup (v' b)⟩ * ⟨_, Y.unipotent_le_besselGroup
    (hu r)⟩⁻¹, ?_⟩) 1 ?_ zero_ne_one (fun g r ↦ ?_) ?_))) (H M l.measurable l')
  repeat' first | apply integrable_of_cocompact C | fun_prop | simp +contextual [*,
    (isMulRightInvariant_of_finite_covolume (isFiniteMeasure_quotMeasure_of_cocompact haar (Γ :=
    (Y.ratBessel.subgroupOf _).subgroupOf _) (C.imp' _
    fun _ ↦ .imp (·.preimage_val o) (· · |>.rec (⟨⟨·, hΓ _ ‹_ ∧ _›.1⟩, ·⟩))))).1, (h1' _).1]
  simp [fun b ↦ by simpa [↓w ⟨_, inv_mem (hu _)⟩] using (hi _
    (Y.inclX_mem_ratBessel g.2) _).trans (k _ (mul_mem (inv_mem (hu g⁻¹)) (v' b)) (p r)), l' _ g.2]
  rw [← (fp _).2, ← quotMean_translate (fp _).1, ← average_quotMeasure_eq_quotMean _ volume,
    integral_sub_average]
  exact (fp _).1.imp (by fun_prop) (by simp +contextual [add_assoc])
