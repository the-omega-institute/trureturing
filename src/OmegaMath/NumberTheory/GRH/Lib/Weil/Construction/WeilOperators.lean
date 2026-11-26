import OmegaMath.NumberTheory.GRH.Lib.Weil.Construction.Model
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: Abstract Weil operators on vacuum coefficients: cocycle, unitarity, intertwining of
Heisenberg action, continuity. -/

noncomputable section

namespace Heisenberg.IsVacuum

open MeasureTheory Heisenberg.Rep ContinuousLinearMap
variable {W : Type _} [AddCommGroup W] [TopologicalSpace W] {H : Heisenberg W} [MeasurableSpace W]
  [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W] {μ : Measure W}
  [μ.IsAddHaarMeasure] {e : W → ℂ} [he : IsVacuum H μ e] {G : Type _} [Group G] [TopologicalSpace G]
  [DistribMulAction G W] [ContinuousSMul G W] {c : G → G → ℂ} (B : H.MultiplierAction μ e G c)
  (A : H.MultiplierAction μ e G) (g : G) (h : G) (k : G) (x) (v : Heisenberg.IsVacuum.Model H)
  (w : Heisenberg.IsVacuum.Model H)

/-- For an action B with any cocycle c and multiplier Δ, and g in G, the bounded operator v ↦
Δ(g) ∫ v(y) ρ(gy)vac dμ(y) on the reproducing space. -/
def weilOp := B.Δ g • (heisRep.moveBy B g).integrated.flip vacElem

lemma integrated_moveBy_integrated : (heisRep.moveBy B g).integrated
  ((heisRep.moveBy B k).integrated w v) x = (heisRep.moveBy B (g * k)).integrated w ((heisRep.moveBy
  B g).integrated v x) := by rw [← flip_apply, map_integrated]; rfl; simp [mul_smul]

lemma map_integrated_moveBy (T : _ →L[ℂ] ℂ) : T ((heisRep.moveBy B g).integrated w v) = ∫ y,
  w (g⁻¹ • y) * T (heisOp y v) ∂μ
  := .trans (by simp [map_integrated_eq_integral]) ((B.2 g).integral_comp' (f := .smul g) _)

lemma weilOp_triple : weilOp B (g * h)⁻¹ * weilOp B g * weilOp B h =
  c g h • 1 := have := (map_integrated_moveBy B (T := modelEval ·))
  hom_ext (by simp_all [← B.7, weilOp, integrated_moveBy_integrated, mul_assoc, smul_smul,
    ← neg_add', he.3, -neg_add_rev, mul_left_comm])

omit [μ.IsAddHaarMeasure] in
lemma norm_integrated_flip_le (R : H.Rep (Model H)) : ‖R.integrated.flip v‖ ≤ ‖v‖ := by
  grw [le_opNorm, opNorm_flip, integrated, kernelIntegral, LinearMap.mkContinuous₂_norm_le] <;> simp

@[simp] lemma modelInner_vacElem : he.modelInner vacElem v =
  v 0 := by simp [← modelInner_heisOp_vacElem]

lemma weilOp_one : weilOp B 1 = 1 := hom_ext (by simp [weilOp, he.2])

/-- Cocycle relation for the Weil operators ω attached to a vacuum e and an action with cocycle
c: if c(g,1) = 1 for all g, then ω(g)ω(h) = c(g,h)·ω(gh). -/
lemma weilOp_mul (h1 : ∀ g, c g 1 = 1) h : weilOp B g * weilOp B h = c g h • weilOp B (g * h) := by
  grind [weilOp_triple B (g * h)⁻¹ 1, weilOp_triple, weilOp_one, =_ mul_smul_one, one_smul, inv_inv]

@[simp] lemma modelInner_weilOp (h1 : c g 1 = 1) : modelInner (weilOp B g v) (weilOp B g w) =
  modelInner v w := by
  convert congr(modelInner ($(weilOp_triple B g 1) v) w) using 1 <;> simp_all [weilOp_one,
    ← conj_modelInner w]
  set u := weilOp B g v; simp [weilOp, map_integrated_moveBy _ g, map_integrated_eq_integral,
    conj_modelInner, ← integral_conj, ← conj_modelInner _ u, mul_comm]

/-- For an action with cocycle c satisfying c(g,1)=1 for all g, the subgroup of those s in G
with c(g,s)=1 for every g. -/
def cocycleRadical (h1 : ∀ g, c g 1 = 1) : Subgroup G := by
  have H g h k := congr(modelInner (weilOp B (g * h * k) vacElem)
    ($(mul_assoc (weilOp B g) (weilOp B h) (weilOp B k)) vacElem))
  simp_all [weilOp_mul, he.2]; use! {s | ∀ g, c g s = 1}, ?_, h1 <;> grind [inv_mul_cancel]

/-- The Weil representation: for an action A with trivial cocycle, the homomorphism from G to
bounded operators sending g to v ↦ Δ(g) ∫ v(y) ρ(gy)vac dμ(y). -/
def weilRep := MonoidHom.mk ⟨_, weilOp_one A⟩ (by simp [weilOp_mul])

lemma modelInner_weilRep : modelInner (weilRep A g v) (weilRep A g w) =
  modelInner v w := by simp [weilRep]

attribute [simp] weilOp modelInner_weilRep

lemma weilRep_heisOp : weilRep A g (heisOp x v) =
  heisOp (g • x) (weilRep A g v) := by simp [weilRep]

lemma weilRep_eq_integral : weilRep A g v = A.Δ g • ∫ y, v (g⁻¹ • y) • heisOp y vacElem ∂μ := by
  rw [← (A.2 g).integral_comp' (f := .smul g)]; aesop

lemma conj_delta_mul_weilRep_vacElem : starRingEnd _ (A.Δ g) * weilRep A g vacElem 0 = 1 := by
  simpa [integrated_moveBy_integrated, he.2] using! congr($(weilOp_triple A 1 g⁻¹) vacElem 0)

@[fun_prop] lemma continuous_weilRep [FirstCountableTopology G] : Continuous ↿(weilRep A · ·) := by
  refine A.4.fst'.smul (continuous_prod_of_continuous_lipschitzWith' _ _ (lipschitzWith_of_opNorm_le
    <| norm_integrated_flip_le _ <| moveBy _ A ·) fun v ↦ continuous_of_dominated ?_ ?_
    (v.2.1.smul_const he.vacElem).norm (.of_forall ?_)) <;> simp [norm_smul] <;> fun_prop

attribute [irreducible] weilRep
