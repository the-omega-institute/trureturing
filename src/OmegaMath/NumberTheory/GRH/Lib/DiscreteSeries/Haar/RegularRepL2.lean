import OmegaMath.NumberTheory.GRH.Lib.DiscreteSeries.Haar.HaarMass
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Haar measure of U(J) in Cayley coordinates, volume of U(n), polynomial volume
growth. Here J is any hermitian matrix with J² = 1, and the normalisation gives U(n) mass one. The
area formula is an inequality for every injective chart after almost every rotation by a unit
scalar, and the covering bound for norm balls holds for any group mapping to U(J), with an explicit
crude constant. Source: L. K. Hua, Harmonic Analysis of Functions of Several Complex Variables in
the Classical Domains (1963), ch. III; I. G. Macdonald, The volume of a compact Lie group, Invent.
Math. 56 (1980); B. Gross, On the motive of a reductive group, Invent. Math. 130 (1997).

This file: Polynomial volume growth of norm balls in closed subgroups; integrability of norm powers.
Right regular representation on L² of U(p,q) is continuous and unitary. -/

open ENNReal Fintype MatMul MeasureTheory Matrix.Norms.L2Operator ContinuousLinearMap LinearIsometry
variable {n} [Fintype.{0} n] {J} [@IsHermInvolution n _ J] {S} [Group.{0} S] [MeasurableSpace S]
  (ν : Measure S)

omit [@IsHermInvolution n _ J] in
lemma IsProperMap.monoidHom_id : IsProperMap (MonoidHom.id (U J)) := by simp

noncomputable instance : MetricSpace (U J) := isClosedEmbedding_U.1.comapMetricSpace _

instance :
    ProperSpace (U J) := ⟨(isClosedEmbedding_U.isCompact_preimage <| isCompact_closedBall ·.1.1 ·)⟩

lemma isCompact_U_norm_le T : IsCompact {y : U J | ‖y.1.1‖ ≤ T} := by simpa only [←
    mem_closedBall_zero_iff] using! isClosedEmbedding_U.isCompact_preimage (isCompact_closedBall ..)

/-- Let ν be a measure on a group S with a topology, positive on nonempty open sets. If f : S →
ℝ is continuous and f(1) < r, the set {s | f(s) ≤ r} has nonzero measure. -/
lemma measure_sublevel_ne_zero [TopologicalSpace S] [ν.IsOpenPosMeasure] {f : S → ℝ} {r} (h :
  f 1 < r := by simp) (c : Continuous f := by fun_prop) :
  ν {s | f s ≤ r} ≠ 0 := (ν.measure_pos_of_mem_nhds (c.tendsto 1 (ge_mem_nhds h))).ne'

variable [MeasurableMul S] [ν.IsMulRightInvariant] (j : S →* U J)

/-- Covering bound: let j: S → U(J) be a group homomorphism, ν right invariant, y∈U(J), D, R ≥ 1,
K ≥ 3DR². Then ν{‖j(s)y‖ ≤ R} ≤ K^{2n²} ν{‖j(s)−1‖ ≤ 1/D} (operator norms). -/
lemma measure_ball_le_covering y {D R K} (h : 1 ≤ D) (hR : 1 ≤ R) (hK : 3 * D * R ^ 2 ≤ K) : ν
    {s | ‖(j s * y).1.1‖ ≤ R} ≤ .ofReal (K ^ (2 * card n ^ 2)) * ν {s | ‖(j s).1.1 - 1‖ ≤ D⁻¹} := by
  let f s := (j s * y).1.1
  have ⟨c, m⟩ := @maxChain_spec {s // ‖f s‖ ≤ R} (D⁻¹ / R ≤ ‖f · - f ·‖)
  have e := encard_le_of_separated (by bound) (by bound) (by
    simpa [IsChain, norm_sub_rev] using c :) fun i _ ↦ i.2
  have := (by simpa using e.trans_lt coe_lt_top :).fintype
  grw [← e.trans (ofReal_le_ofReal _), ← tsum_set_const, ← tsum_congr (measure_preimage_mul_right _
    ·.1⁻¹ _), ← measure_iUnion_le, measure_mono]; simp_intro g b; by_contra! H
  refine (H _ ⟨b, m (c.insert fun k a _ ↦ .inl ?_) (by simp) ▸ .inl rfl⟩).not_ge ?_
  grw [div_le_iff₀ (by bound), H _ ⟨k.2, a⟩, ← k.2, ← U.norm_inv (j k * y), ← norm_mul_le]
  repeat simp +arith [f, h.trans', Module.finrank_matrix, ← sq, division_def]
  gcongr; nlinarith

variable {j : S →* U J} [TopologicalSpace S] [IsFiniteMeasureOnCompacts ν] (hj : IsProperMap j)
  [BorelSpace S] [Nonempty n] {c} (hc : 8 * card n ^ 2 < c)

omit [MeasurableMul S] [ν.IsMulRightInvariant] [BorelSpace S] [Nonempty n] in
lemma measure_ball_ne_top_of_isProperMap (hj : IsProperMap j) R :
  ν {s | ‖(j s).1.1 - 1‖ ≤ R} ≠ ⊤ := by
  simpa [← dist_eq_norm] using! (hj.isCompact_preimage (isCompact_closedBall 1 R)).measure_ne_top

include hj hc

/-- Let j : S → U(J) be a proper group homomorphism, J a hermitian involution of size n ≥ 1, ν right
invariant, finite on compacts, c > 8n² natural, y∈U(J). Then (2/‖j(s)y‖)^c is ν-integrable with
integral ≤ 16^c·ν{‖j(s)−1‖ ≤ 1} (operator norms). -/
lemma integral_decay_le y : letI f s := (2 / ‖(j s * y).1.1‖) ^ c
  Integrable f ν ∧ ∫ s, f s ∂ν ≤ 16 ^ c * ν.real {s | ‖(j s).1.1 - 1‖ ≤ 1} := by
  have := integral_rpow_neg_le_of_layers c (fun _ ↦ U.one_le_norm _) (fun R ↦
    (measure_ball_le_covering ν j y le_rfl ·
    le_rfl)) 3 (measure_ball_ne_top_of_isProperMap ν hj _) (Continuous.measurable (by fun_prop))
  simp_all [mul_pow, division_def, Integrable.const_mul]
  grw [this.2, ← pow_succ, (_ : _ + 1 ≤ c), ← mul_assoc, ← mul_pow] <;> bound

lemma lintegral_decay_le y : ∫⁻ s, .ofReal ((2 / ‖(j s * y).1.1‖) ^ c) ∂ν ≤ .ofReal (16 ^ c) * ν
    {s | ‖(j s).1.1 - 1‖ ≤ 1} := (integral_decay_le ν hj hc y).rec (by grw [←
 ofReal_integral_eq_lintegral_ofReal · (.of_forall
  _), ·] <;> simp [measure_ball_ne_top_of_isProperMap, *, field])

omit hj hc

/-- The action of U(diag ε) by right translation on the space of complex-valued L² functions on
U(diag ε), as a homomorphism to bounded operators. -/
noncomputable def rightRegularL2 {n} [Fintype n] {ε : n → _} :
  USign ε →* (USign ε →₂[volume] ℂ) →L[ℂ] USign ε
  →₂[volume] ℂ := ⟨⟨((DomMulAct.mk ∘ MulOpposite.op) · • 1), by simp⟩, fun x y ↦
    ContinuousLinearMap.ext fun f ↦
    (inferInstance : MulAction (USign ε)ᵐᵒᵖᵈᵐᵃ _).mul_smul ⟨⟨x⟩⟩ ⟨⟨y⟩⟩ f⟩

lemma isUnitaryRep_rightRegularL2 {n} [Fintype n] {ε : n → _} : IsUnitaryRep 0 (rightRegularL2 (ε :=
  ε)) (innerSL ℂ) := by use fun _ ↦ continuous_const.compMeasurePreservingLp (Mul.mul
  ContinuousMap.snd .fst).curry.2 _ ?_, (inner_map_map
  ⟨rightRegularL2 · |>.1, ?_⟩), ?_, ?_, 1 <;> simp [rightRegularL2, sq, opNorm_le_iff]
