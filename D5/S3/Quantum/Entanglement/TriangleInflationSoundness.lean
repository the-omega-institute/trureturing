/- GID: D5/S3/Quantum/Entanglement/TriangleInflationSoundness
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/TriangleInflationSoundness
   mirror-E: none(waiver:continuous-triangle-local-lift)
   anchors: []
   utility: none
   digest: Continuous triangle-local responses generate finite observable inflation laws on independent source copies. -/

import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Integration
import D5.S3.Quantum.Entanglement.TriangleSymmetricLocalRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Quantum.Entanglement.TriangleInflationSoundness

open MeasureTheory Set
open scoped BigOperators
open ProbabilityTheory
open D5.S3.Quantum.Entanglement.TriangleSymmetricLocalRefutation

abbrev Party := Fin 3
abbrev Outcome := Fin 4

/-- The continuous stochastic response data occurring in `IsTriangleLocal`.
Party 0 is A with inputs β,γ; party 1 is B with γ,α; party 2 is C with α,β. -/
structure ResponseModel where
  response : Party → Outcome → ℝ → ℝ → ℝ
  measurable : ∀ v a, Measurable (Function.uncurry (response v a))
  nonnegative : ∀ v a x y, 0 ≤ response v a x y
  normalized : ∀ v x y, ∑ a, response v a x y = 1

variable {Copy Node : Type*} [Fintype Copy] [Fintype Node]
  [DecidableEq Copy] [DecidableEq Node]

/-- Each node is a copy of a fixed party and chooses one copy of each of
that party's two incident source types.  An A node cannot be wired to α. -/
structure InflationSpec (Copy Node : Type*) where
  party : Node → Party
  firstCopy : Node → Copy
  secondCopy : Node → Copy

abbrev Source (Copy : Type*) := Party × Copy
abbrev SourceState (Copy : Type*) := Source Copy → ℝ

def InflationSpec.firstSource (S : InflationSpec Copy Node) (v : Node) : Source Copy :=
  (S.party v + 1, S.firstCopy v)

def InflationSpec.secondSource (S : InflationSpec Copy Node) (v : Node) : Source Copy :=
  (S.party v + 2, S.secondCopy v)

def unitSource : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

private theorem unitSource_univ : unitSource Set.univ = 1 := by
  simp [unitSource, Measure.restrict_apply_univ, Real.volume_Icc]

instance : IsProbabilityMeasure unitSource := ⟨unitSource_univ⟩

/-- The actual product measure of independent continuous source copies. -/
def sourceMeasure (Copy : Type*) [Fintype Copy] : Measure (SourceState Copy) :=
  Measure.pi (fun _ : Source Copy => unitSource)

instance : IsProbabilityMeasure (sourceMeasure Copy) := by
  unfold sourceMeasure
  infer_instance

def nodeResponse (S : InflationSpec Copy Node) (R : ResponseModel)
    (v : Node) (a : Outcome) (u : SourceState Copy) : ℝ :=
  R.response (S.party v) a (u (S.firstSource v)) (u (S.secondSource v))

private theorem nodeResponse_measurable (S : InflationSpec Copy Node) (R : ResponseModel)
    (v : Node) (a : Outcome) : Measurable (nodeResponse S R v a) := by
  change Measurable (fun u : SourceState Copy =>
    R.response (S.party v) a (u (S.firstSource v)) (u (S.secondSource v)))
  have hm : Measurable (fun u : SourceState Copy =>
      (u (S.firstSource v), u (S.secondSource v))) :=
    (measurable_pi_apply (S.firstSource v)).prodMk
      (measurable_pi_apply (S.secondSource v))
  simpa only [Function.comp_def, Function.uncurry] using
    (R.measurable (S.party v) a).comp hm

private theorem nodeResponse_bounds (S : InflationSpec Copy Node) (R : ResponseModel)
    (v : Node) (a : Outcome) (u : SourceState Copy) :
    0 ≤ nodeResponse S R v a u ∧ nodeResponse S R v a u ≤ 1 := by
  refine ⟨R.nonnegative _ _ _ _, ?_⟩
  have h := Finset.single_le_sum
    (fun b _ => R.nonnegative (S.party v) b (u (S.firstSource v)) (u (S.secondSource v)))
    (show a ∈ (Finset.univ : Finset Outcome) from Finset.mem_univ _)
  simpa [nodeResponse, R.normalized] using h

/-- Conditional probability of an observable assignment, given the actual
source copies; copied observable nodes are conditionally independent draws. -/
def cellWeight (S : InflationSpec Copy Node) (R : ResponseModel)
    (o : Node → Outcome) (u : SourceState Copy) : ℝ :=
  ∏ v, nodeResponse S R v (o v) u

private theorem cellWeight_measurable (S : InflationSpec Copy Node) (R : ResponseModel)
    (o : Node → Outcome) : Measurable (cellWeight S R o) := by
  exact Finset.measurable_prod _ (fun v _ => nodeResponse_measurable S R v (o v))

private theorem cellWeight_bounds (S : InflationSpec Copy Node) (R : ResponseModel)
    (o : Node → Outcome) (u : SourceState Copy) :
    0 ≤ cellWeight S R o u ∧ cellWeight S R o u ≤ 1 := by
  classical
  exact ⟨Finset.prod_nonneg (fun v _ => (nodeResponse_bounds S R v (o v) u).1),
    Finset.prod_le_one₀ (fun v _ => (nodeResponse_bounds S R v (o v) u).1)
      (fun v _ => (nodeResponse_bounds S R v (o v) u).2)⟩

private theorem cellWeight_integrable (S : InflationSpec Copy Node) (R : ResponseModel)
    (o : Node → Outcome) : Integrable (cellWeight S R o) (sourceMeasure Copy) := by
  apply Integrable.of_bound (cellWeight_measurable S R o).aestronglyMeasurable 1
  filter_upwards with u
  have h := cellWeight_bounds S R o u
  simpa [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

/-- The finite observable law induced by the continuous product-source lift. -/
def inflationMass (S : InflationSpec Copy Node) (R : ResponseModel)
    (o : Node → Outcome) : ℝ :=
  ∫ u, cellWeight S R o u ∂sourceMeasure Copy

theorem inflationMass_nonnegative (S : InflationSpec Copy Node) (R : ResponseModel)
    (o : Node → Outcome) : 0 ≤ inflationMass S R o := by
  exact integral_nonneg (fun u => (cellWeight_bounds S R o u).1)

theorem inflationMass_normalized (S : InflationSpec Copy Node) (R : ResponseModel) :
    ∑ o : Node → Outcome, inflationMass S R o = 1 := by
  classical
  unfold inflationMass
  rw [← integral_finsetSum _ (fun o _ => cellWeight_integrable S R o)]
  have hpoint : ∀ u : SourceState Copy, ∑ o : Node → Outcome, cellWeight S R o u = 1 := by
    intro u
    unfold cellWeight
    rw [← Fintype.prod_sum (fun v a => nodeResponse S R v a u)]
    simp [nodeResponse, R.normalized]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  simp

/-- The original continuous triangle integral represented by these responses. -/
def Represents (R : ResponseModel) (p : Outcome → Outcome → Outcome → ℝ) : Prop :=
  ∀ a b c, p a b c = ∫ t in Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1),
    R.response 0 a t.2.1 t.2.2 * R.response 1 b t.2.2 t.1 *
      R.response 2 c t.1 t.2.1

theorem isTriangleLocal_responseModel
    (p : Outcome → Outcome → Outcome → ℝ) (hp : IsTriangleLocal p) :
    ∃ R : ResponseModel, Represents R p := by
  rcases hp with ⟨pA, pB, pC, hmA, hmB, hmC, hnA, hnB, hnC, hsA, hsB, hsC, heq⟩
  let R : ResponseModel :=
    { response := ![pA, pB, pC]
      measurable := by intro v a; fin_cases v <;> simp [hmA, hmB, hmC]
      nonnegative := by intro v a x y; fin_cases v <;> simp [hnA, hnB, hnC]
      normalized := by intro v x y; fin_cases v <;> simp [hsA, hsB, hsC] }
  exact ⟨R, heq⟩

/-- The reduced conditional observable law on a finite node block. -/
def blockWeight (S : InflationSpec Copy Node) (R : ResponseModel)
    (J : Finset Node) (o : Node → Outcome) (u : SourceState Copy) : ℝ :=
  ∏ v ∈ J, nodeResponse S R v (o v) u

def marginalMass (S : InflationSpec Copy Node) (R : ResponseModel)
    (J : Finset Node) (o : Node → Outcome) : ℝ :=
  ∫ u, blockWeight S R J o u ∂sourceMeasure Copy

private theorem blockWeight_measurable (S : InflationSpec Copy Node) (R : ResponseModel)
    (J : Finset Node) (o : Node → Outcome) : Measurable (blockWeight S R J o) :=
  Finset.measurable_prod J (fun v _ => nodeResponse_measurable S R v (o v))

private theorem blockWeight_integrable (S : InflationSpec Copy Node) (R : ResponseModel)
    (J : Finset Node) (o : Node → Outcome) :
    Integrable (blockWeight S R J o) (sourceMeasure Copy) := by
  apply Integrable.of_bound (blockWeight_measurable S R J o).aestronglyMeasurable 1
  filter_upwards with u
  have hn : 0 ≤ blockWeight S R J o u :=
    Finset.prod_nonneg (fun v _ => (nodeResponse_bounds S R v (o v) u).1)
  have hle : blockWeight S R J o u ≤ 1 :=
    Finset.prod_le_one₀ (fun v _ => (nodeResponse_bounds S R v (o v) u).1)
      (fun v _ => (nodeResponse_bounds S R v (o v) u).2)
  simpa [Real.norm_eq_abs, abs_of_nonneg hn] using hle

/-- Marginalizing the actual full lift removes precisely the unobserved
response factors. The retained marginal is derived, not supplied. -/
theorem inflationMass_marginal
    (S : InflationSpec Copy Node) (R : ResponseModel)
    (J : Finset Node) (o : Node → Outcome) :
    (∑ z : {v : Node // v ∉ J} → Outcome,
      inflationMass S R ((Equiv.piEquivPiSubtypeProd
        (fun v => v ∈ J) (fun _ => Outcome)).symm
          ((fun v : {v : Node // v ∈ J} => o v), z))) = marginalMass S R J o := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun v : Node => v ∈ J) (fun _ => Outcome)
  let ext (z : {v : Node // v ∉ J} → Outcome) :=
    e.symm ((fun v : {v : Node // v ∈ J} => o v), z)
  change (∑ z, ∫ u, cellWeight S R (ext z) u ∂sourceMeasure Copy) =
    ∫ u, blockWeight S R J o u ∂sourceMeasure Copy
  rw [← integral_finsetSum _ (fun z _ => cellWeight_integrable S R (ext z))]
  apply integral_congr_ae
  filter_upwards with u
  have hsplit : ∀ z, cellWeight S R (ext z) u =
      blockWeight S R J o u *
        ∏ v : {v : Node // v ∉ J}, nodeResponse S R v (z v) u := by
    intro z
    unfold cellWeight
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun v : Node => v ∈ J)]
    congr 1
    · have hext (v : J) : ext z v = o v := by
        have h := congrFun (congrArg Prod.fst (e.apply_symm_apply
          ((fun v : {v : Node // v ∈ J} => o v), z))) v
        exact h
      simp_rw [hext]
      exact (Finset.prod_subtype J (fun _ => Iff.rfl)
        (fun v : Node => nodeResponse S R v (o v) u)).symm
    · apply Finset.prod_congr rfl
      intro v _
      have h := congrFun (congrArg Prod.snd (e.apply_symm_apply
        ((fun v : {v : Node // v ∈ J} => o v), z))) v
      change ext z v = z v at h
      rw [h]
  simp_rw [hsplit]
  rw [← Finset.mul_sum, ← Fintype.prod_sum
    (fun (v : {v : Node // v ∉ J}) (a : Outcome) => nodeResponse S R v a u)]
  simp [nodeResponse, R.normalized]

/-- Summing one retained observable removes its stochastic response factor. -/
theorem marginalMass_sum_insert
    (S : InflationSpec Copy Node) (R : ResponseModel)
    (J : Finset Node) (v : Node) (o : Node → Outcome) (hv : v ∉ J) :
    (∑ a : Outcome, marginalMass S R (insert v J) (Function.update o v a)) =
      marginalMass S R J o := by
  classical
  unfold marginalMass
  rw [← integral_finsetSum _ (fun a _ => blockWeight_integrable S R _ _)]
  apply integral_congr_ae
  filter_upwards with u
  have hpoint (a : Outcome) :
      blockWeight S R (insert v J) (Function.update o v a) u =
        nodeResponse S R v a u * blockWeight S R J o u := by
    unfold blockWeight
    rw [Finset.prod_insert hv, Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro w hw
    rw [Function.update_of_ne (by intro h; exact hv (h ▸ hw))]
  simp_rw [hpoint]
  rw [← Finset.sum_mul]
  simp [nodeResponse, R.normalized]

/-- The exact source coordinates used by a block of observable nodes. -/
def sourceSupport (S : InflationSpec Copy Node) (J : Finset Node) : Finset (Source Copy) :=
  J.biUnion (fun v => {S.firstSource v, S.secondSource v})

private theorem firstSource_mem (S : InflationSpec Copy Node)
    (J : Finset Node) (v : J) : S.firstSource v ∈ sourceSupport S J := by
  simp only [sourceSupport, Finset.mem_biUnion]
  exact ⟨v, v.property, by simp⟩

private theorem secondSource_mem (S : InflationSpec Copy Node)
    (J : Finset Node) (v : J) : S.secondSource v ∈ sourceSupport S J := by
  simp only [sourceSupport, Finset.mem_biUnion]
  exact ⟨v, v.property, by simp⟩

private def reducedBlockWeight (S : InflationSpec Copy Node) (R : ResponseModel)
    (J : Finset Node) (o : Node → Outcome) (u : sourceSupport S J → ℝ) : ℝ :=
  ∏ v : J, R.response (S.party v) (o v)
    (u ⟨S.firstSource v, firstSource_mem S J v⟩)
    (u ⟨S.secondSource v, secondSource_mem S J v⟩)

private theorem reducedBlockWeight_measurable (S : InflationSpec Copy Node) (R : ResponseModel)
    (J : Finset Node) (o : Node → Outcome) : Measurable (reducedBlockWeight S R J o) := by
  apply Finset.measurable_prod
  intro v _
  have hm : Measurable (fun u : sourceSupport S J → ℝ =>
      (u ⟨S.firstSource v, firstSource_mem S J v⟩,
        u ⟨S.secondSource v, secondSource_mem S J v⟩)) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  exact (R.measurable (S.party v) (o v)).comp hm

private theorem blockWeight_restrict (S : InflationSpec Copy Node) (R : ResponseModel)
    (J : Finset Node) (o : Node → Outcome) (u : SourceState Copy) :
    blockWeight S R J o u =
      reducedBlockWeight S R J o (fun i => u i) := by
  unfold reducedBlockWeight
  change blockWeight S R J o u = ∏ v : J, nodeResponse S R v (o v) u
  exact (Finset.prod_coe_sort J (fun v : Node => nodeResponse S R v (o v) u)).symm

/-- Disjoint source supports make arbitrary retained observable groups
independent under the same continuous lift, including unknown marginals. -/
theorem marginalMass_disjoint_source_factorization
    (S : InflationSpec Copy Node) (R : ResponseModel)
    (J K : Finset Node) (o : Node → Outcome)
    (hJK : Disjoint J K) (hsource : Disjoint (sourceSupport S J) (sourceSupport S K)) :
    marginalMass S R (J ∪ K) o = marginalMass S R J o * marginalMass S R K o := by
  have hind : iIndepFun (fun i : Source Copy => fun u : SourceState Copy => u i)
      (sourceMeasure Copy) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hblocks := hind.indepFun_finset (sourceSupport S J) (sourceSupport S K)
    hsource (fun i => measurable_pi_apply i)
  have hweights := hblocks.comp (reducedBlockWeight_measurable S R J o)
    (reducedBlockWeight_measurable S R K o)
  have hw : IndepFun (blockWeight S R J o) (blockWeight S R K o) (sourceMeasure Copy) := by
    convert hweights using 1 <;> funext u <;> exact blockWeight_restrict S R _ o u
  unfold marginalMass
  have hpoint : ∀ u, blockWeight S R (J ∪ K) o u =
      blockWeight S R J o u * blockWeight S R K o u := by
    intro u
    exact Finset.prod_union hJK
  simp_rw [hpoint]
  exact hw.integral_fun_mul_eq_mul_integral
    (blockWeight_measurable S R J o).aestronglyMeasurable
    (blockWeight_measurable S R K o).aestronglyMeasurable

/-- Selecting one copy of each source type has exactly the original
continuous triple-source law. All other source copies integrate out. -/
theorem sourceMeasure_map_triangle (α β γ : Copy) :
    (sourceMeasure Copy).map (fun u => (u (0, α), (u (1, β), u (2, γ)))) =
      unitSource.prod (unitSource.prod unitSource) := by
  have hind : iIndepFun (fun i : Source Copy => fun u : SourceState Copy => u i)
      (sourceMeasure Copy) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have heval (i : Source Copy) :
      (sourceMeasure Copy).map (fun u => u i) = unitSource :=
    (measurePreserving_eval (fun _ : Source Copy => unitSource) i).map_eq
  have hpair : IndepFun (fun u : SourceState Copy => u (1, β))
      (fun u => u (2, γ)) (sourceMeasure Copy) :=
    hind.indepFun (by
      intro h
      have := congrArg (fun i : Source Copy => i.1.val) h
      norm_num at this)
  have htriple := (hind.indepFun_prodMk (fun i => measurable_pi_apply i)
    (1, β) (2, γ) (0, α)
    (by intro h; have := congrArg (fun i : Source Copy => i.1.val) h; norm_num at this)
    (by intro h; have := congrArg (fun i : Source Copy => i.1.val) h; norm_num at this)).symm
  rw [htriple.map_prod_eq_prod_map_map (measurable_pi_apply _).aemeasurable
    ((measurable_pi_apply _).prodMk (measurable_pi_apply _)).aemeasurable,
    hpair.map_prod_eq_prod_map_map (measurable_pi_apply _).aemeasurable
      (measurable_pi_apply _).aemeasurable, heval, heval, heval]

private def triangleWeight (R : ResponseModel) (a b c : Outcome)
    (t : ℝ × (ℝ × ℝ)) : ℝ :=
  R.response 0 a t.2.1 t.2.2 * R.response 1 b t.2.2 t.1 *
    R.response 2 c t.1 t.2.1

private theorem triangleWeight_measurable (R : ResponseModel) (a b c : Outcome) :
    Measurable (triangleWeight R a b c) := by
  exact ((R.measurable 0 a).comp (measurable_snd.fst.prodMk measurable_snd.snd)).mul
    ((R.measurable 1 b).comp (measurable_snd.snd.prodMk measurable_fst)) |>.mul
      ((R.measurable 2 c).comp (measurable_fst.prodMk measurable_snd.fst))

/-- Every correctly connected copied triangle has the original observed
distribution, for arbitrary measurable stochastic responses on `[0,1]`. -/
theorem marginalMass_triangle
    (S : InflationSpec Copy Node) (R : ResponseModel)
    (p : Outcome → Outcome → Outcome → ℝ) (hp : Represents R p)
    (vA vB vC : Node) (α β γ : Copy) (o : Node → Outcome)
    (hA : S.party vA = 0) (hB : S.party vB = 1) (hC : S.party vC = 2)
    (hA₁ : S.firstCopy vA = β) (hA₂ : S.secondCopy vA = γ)
    (hB₁ : S.firstCopy vB = γ) (hB₂ : S.secondCopy vB = α)
    (hC₁ : S.firstCopy vC = α) (hC₂ : S.secondCopy vC = β) :
    marginalMass S R {vA, vB, vC} o = p (o vA) (o vB) (o vC) := by
  have hAB : vA ≠ vB := by
    intro h; have := congrArg Fin.val (hA.symm.trans (h ▸ hB)); norm_num at this
  have hAC : vA ≠ vC := by
    intro h; have := congrArg Fin.val (hA.symm.trans (h ▸ hC)); norm_num at this
  have hBC : vB ≠ vC := by
    intro h; have := congrArg Fin.val (hB.symm.trans (h ▸ hC)); norm_num at this
  have hpoint (u : SourceState Copy) : blockWeight S R {vA, vB, vC} o u =
      triangleWeight R (o vA) (o vB) (o vC)
        (u (0, α), (u (1, β), u (2, γ))) := by
    simp [blockWeight, nodeResponse, InflationSpec.firstSource,
      InflationSpec.secondSource, hAB, hAC, hBC, hA, hB, hC,
      hA₁, hA₂, hB₁, hB₂, hC₁, hC₂, triangleWeight, mul_assoc]
  unfold marginalMass
  simp_rw [hpoint]
  rw [← integral_map ((measurable_pi_apply _).prodMk
    ((measurable_pi_apply _).prodMk (measurable_pi_apply _))).aemeasurable
      (triangleWeight_measurable R _ _ _).aestronglyMeasurable,
    sourceMeasure_map_triangle]
  rw [hp]
  congr 1
  rw [unitSource, Measure.prod_restrict, Measure.prod_restrict]
  rfl

/-- The one-party admissible marginal follows by summing the two other
outcomes of a genuinely lifted triangle. -/
theorem marginalMass_singleton_A
    (S : InflationSpec Copy Node) (R : ResponseModel)
    (p : Outcome → Outcome → Outcome → ℝ) (hp : Represents R p)
    (vA vB vC : Node) (α β γ : Copy) (o : Node → Outcome)
    (hA : S.party vA = 0) (hB : S.party vB = 1) (hC : S.party vC = 2)
    (hA₁ : S.firstCopy vA = β) (hA₂ : S.secondCopy vA = γ)
    (hB₁ : S.firstCopy vB = γ) (hB₂ : S.secondCopy vB = α)
    (hC₁ : S.firstCopy vC = α) (hC₂ : S.secondCopy vC = β) :
    marginalMass S R {vA} o = ∑ b : Outcome, ∑ c : Outcome, p (o vA) b c := by
  have hAB : vA ≠ vB := by
    intro h; have := congrArg Fin.val (hA.symm.trans (h ▸ hB)); norm_num at this
  have hAC : vA ≠ vC := by
    intro h; have := congrArg Fin.val (hA.symm.trans (h ▸ hC)); norm_num at this
  have hBC : vB ≠ vC := by
    intro h; have := congrArg Fin.val (hB.symm.trans (h ▸ hC)); norm_num at this
  have hsmall := marginalMass_sum_insert S R {vA} vB o
    (by simpa using hAB.symm)
  rw [Finset.pair_comm vB vA] at hsmall
  have hlarge (b : Outcome) := marginalMass_sum_insert S R {vA, vB} vC
    (Function.update o vB b) (by simp [hAC.symm, hBC.symm])
  have hset : insert vC ({vA, vB} : Finset Node) = {vA, vB, vC} := by
    ext v
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  simp_rw [hset] at hlarge
  have htri (b c : Outcome) :
      marginalMass S R {vA, vB, vC}
        (Function.update (Function.update o vB b) vC c) = p (o vA) b c := by
    simpa [hAB, hAC, hBC] using marginalMass_triangle S R p hp vA vB vC α β γ
      (Function.update (Function.update o vB b) vC c)
      hA hB hC hA₁ hA₂ hB₁ hB₂ hC₁ hC₂
  rw [← hsmall]
  simp_rw [← hlarge, htri]

/-- Summing the A and C outcomes gives the B-party admissible marginal. -/
theorem marginalMass_singleton_B
    (S : InflationSpec Copy Node) (R : ResponseModel)
    (p : Outcome → Outcome → Outcome → ℝ) (hp : Represents R p)
    (vA vB vC : Node) (α β γ : Copy) (o : Node → Outcome)
    (hA : S.party vA = 0) (hB : S.party vB = 1) (hC : S.party vC = 2)
    (hA₁ : S.firstCopy vA = β) (hA₂ : S.secondCopy vA = γ)
    (hB₁ : S.firstCopy vB = γ) (hB₂ : S.secondCopy vB = α)
    (hC₁ : S.firstCopy vC = α) (hC₂ : S.secondCopy vC = β) :
    marginalMass S R {vB} o = ∑ a : Outcome, ∑ c : Outcome, p a (o vB) c := by
  have hAB : vA ≠ vB := by
    intro h; have := congrArg Fin.val (hA.symm.trans (h ▸ hB)); norm_num at this
  have hAC : vA ≠ vC := by
    intro h; have := congrArg Fin.val (hA.symm.trans (h ▸ hC)); norm_num at this
  have hBC : vB ≠ vC := by
    intro h; have := congrArg Fin.val (hB.symm.trans (h ▸ hC)); norm_num at this
  have hsmall := marginalMass_sum_insert S R {vB} vA o (by simpa using hAB)
  have hlarge (a : Outcome) := marginalMass_sum_insert S R {vA, vB} vC
    (Function.update o vA a) (by simp [hAC.symm, hBC.symm])
  have hset : insert vC ({vA, vB} : Finset Node) = {vA, vB, vC} := by
    ext v
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  simp_rw [hset] at hlarge
  have htri (a c : Outcome) :
      marginalMass S R {vA, vB, vC}
        (Function.update (Function.update o vA a) vC c) = p a (o vB) c := by
    simpa [hAB.symm, hBC, hAC] using marginalMass_triangle S R p hp vA vB vC α β γ
      (Function.update (Function.update o vA a) vC c)
      hA hB hC hA₁ hA₂ hB₁ hB₂ hC₁ hC₂
  rw [← hsmall]
  simp_rw [← hlarge, htri]

/-- Summing the A and B outcomes gives the C-party admissible marginal. -/
theorem marginalMass_singleton_C
    (S : InflationSpec Copy Node) (R : ResponseModel)
    (p : Outcome → Outcome → Outcome → ℝ) (hp : Represents R p)
    (vA vB vC : Node) (α β γ : Copy) (o : Node → Outcome)
    (hA : S.party vA = 0) (hB : S.party vB = 1) (hC : S.party vC = 2)
    (hA₁ : S.firstCopy vA = β) (hA₂ : S.secondCopy vA = γ)
    (hB₁ : S.firstCopy vB = γ) (hB₂ : S.secondCopy vB = α)
    (hC₁ : S.firstCopy vC = α) (hC₂ : S.secondCopy vC = β) :
    marginalMass S R {vC} o = ∑ a : Outcome, ∑ b : Outcome, p a b (o vC) := by
  have hAB : vA ≠ vB := by
    intro h; have := congrArg Fin.val (hA.symm.trans (h ▸ hB)); norm_num at this
  have hAC : vA ≠ vC := by
    intro h; have := congrArg Fin.val (hA.symm.trans (h ▸ hC)); norm_num at this
  have hBC : vB ≠ vC := by
    intro h; have := congrArg Fin.val (hB.symm.trans (h ▸ hC)); norm_num at this
  have hsmall := marginalMass_sum_insert S R {vC} vA o (by simpa using hAC)
  have hlarge (a : Outcome) := marginalMass_sum_insert S R {vA, vC} vB
    (Function.update o vA a) (by simp [hAB.symm, hBC])
  have hset : insert vB ({vA, vC} : Finset Node) = {vA, vB, vC} := by
    ext v
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  simp_rw [hset] at hlarge
  have htri (a b : Outcome) :
      marginalMass S R {vA, vB, vC}
        (Function.update (Function.update o vA a) vB b) = p a b (o vC) := by
    simpa [hAB, hAC.symm, hBC.symm] using marginalMass_triangle S R p hp vA vB vC α β γ
      (Function.update (Function.update o vA a) vB b)
      hA hB hC hA₁ hA₂ hB₁ hB₂ hC₁ hC₂
  rw [← hsmall]
  simp_rw [← hlarge, htri]

/-- A simultaneous permutation of source copies and the correspondingly
wired observable nodes preserves the actual lifted observable law. -/
theorem inflationMass_copy_symmetry
    (S : InflationSpec Copy Node) (R : ResponseModel)
    (π : Node ≃ Node) (τ : Source Copy ≃ Source Copy)
    (hparty : ∀ v, S.party (π v) = S.party v)
    (hfirst : ∀ v, S.firstSource (π v) = τ (S.firstSource v))
    (hsecond : ∀ v, S.secondSource (π v) = τ (S.secondSource v))
    (o : Node → Outcome) : inflationMass S R (o ∘ π) = inflationMass S R o := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Source Copy => ℝ) τ
  have hmeasure : MeasurePreserving e (sourceMeasure Copy) (sourceMeasure Copy) :=
    measurePreserving_piCongrLeft (fun _ => unitSource) τ
  have hpoint (u : SourceState Copy) :
      cellWeight S R (o ∘ π) u = cellWeight S R o (e u) := by
    calc
      _ = ∏ v, nodeResponse S R (π v) (o (π v)) (e u) := by
        apply Finset.prod_congr rfl
        intro v _
        simp only [nodeResponse, Function.comp_apply, hparty, hfirst, hsecond, e,
          MeasurableEquiv.piCongrLeft_apply_apply]
      _ = cellWeight S R o (e u) :=
        π.prod_comp (fun v : Node => nodeResponse S R v (o v) (e u))
  unfold inflationMass
  simp_rw [hpoint]
  exact hmeasure.integral_comp' _

end D5.S3.Quantum.Entanglement.TriangleInflationSoundness
