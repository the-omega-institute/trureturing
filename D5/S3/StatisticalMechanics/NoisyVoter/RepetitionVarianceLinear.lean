/- GID: D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Noisy voter repetition counts have a positive linear variance lower bound. -/

/-
proof_shape: result: content
escape_witness: local_erasure
admission_basis: open-problem-resolution (#16646; Proved)
Direct frozen dependency: D5/S3/Combinatorics/IsingUniquenessSets.sgn
  declaration statement_id: sha256:1589788918111821cb994915047b9b43151423396895fcfd849105cc8fe4d481.
Same-delivery shared-owner theorem: D5/S3/Combinatorics/IsingUniquenessSets.sgn_not
  declaration statement_id: sha256:3fea0d0608c561a90f61ba97d2e868ba6d838b7ae89eb97cdd74a8310505d819.
The closed claim uses the coordinate encoding of issue #16646 and no additional instances.
The explicit bound is private and is consumed by result.
The sign map and negation identity use IsingUniquenessSets; product laws use Measure.infinitePi.
The coordinate action uses Function.update and Pi.map.
Neighbour singleton measurability uses Mathlib's discrete-space instance.
Escape registration of result and the shared sgn_not theorem is unfinished:
  https://github.com/the-omega-institute/trureturing/issues/16773.
Declaration rows: name | proof_shape | escape_witness | direct consumers.
Names without a prefix belong to this module. Constructions are not theorem classifications.
Consumers are read from the elaborated values; generated instance and projection uses are included.
The four witnesses nvm_measurable, local_erasure, nvm_before_flip and nvm_sample_eq
are induction statements beyond instantiation and normalization of existing premises.
Coord | construction | none | Coord.casesOn,Coord.choice.elim,Coord.choice.inj,Coord.choice.injEq,Coord.choice.noConfusion,Coord.ctorElim,Coord.ctorElimType,Coord.ctorIdx,Coord.fresh.elim,Coord.fresh.inj,Coord.fresh.injEq,Coord.fresh.noConfusion,Coord.initial.elim,Coord.initial.inj,Coord.initial.injEq,Coord.initial.noConfusion,Coord.noConfusion,Coord.noConfusionType,Coord.recOn,Coord.refresh.elim,Coord.refresh.inj,Coord.refresh.injEq,Coord.refresh.noConfusion,Model.casesOn,Model.mk.inj,Model.mk.injEq,Model.mk.noConfusion,Model.mk.sizeOf_spec,Model.noConfusion,Model.noConfusionType,Model.recOn,Value,W,W_bound,W_measurable,W_memLp,W_sample_eq,coefficient,coordinateLaw,coordinateLaw.congr_simp,coordinateLawProbability,erased,erased_flip,erased_measurable,extraRefresh,extraRefresh_measurable,extraRefresh_prob,flipFresh,flipFresh_involutive,flipFresh_preserving,flipFresh_sameExcept,flipValue,good,good_bound,good_flip_pair,good_integral,good_measurable,instDecidableEqCoord.decEq,integral_flip,local_erasure,local_statistic_difference,model_W_map,model_W_variance,model_explicitBound,model_joint_law,nvm,nvm.eq_def,nvm_before_flip,nvm_measurable,nvm_sample_eq,product_explicitBound,refresh_coordinate_prob,repetition,sameExcept,valueDiscrete,valueFinite,valueMeasurable,witness,witness_bound,witness_covariance,witness_flip_other,witness_flip_self,witness_mean_zero,witness_measurable,witness_memLp,witness_orthogonal,witness_projection_pointwise,witness_square,witness_variance_lower
Value | construction | none | Model.casesOn,Model.mk.inj,Model.mk.injEq,Model.mk.noConfusion,Model.mk.sizeOf_spec,Model.noConfusion,Model.noConfusionType,Model.recOn,W,W_bound,W_measurable,W_memLp,W_sample_eq,coefficient,coordinateLaw,coordinateLaw.congr_simp,coordinateLawProbability,erased,erased_flip,erased_measurable,extraRefresh,extraRefresh_measurable,extraRefresh_prob,flipFresh,flipFresh_involutive,flipFresh_preserving,flipFresh_sameExcept,flipValue,good,good_bound,good_flip_pair,good_integral,good_measurable,integral_flip,local_erasure,local_statistic_difference,model_W_map,model_W_variance,model_explicitBound,model_joint_law,nvm,nvm.eq_def,nvm_before_flip,nvm_measurable,nvm_sample_eq,product_explicitBound,refresh_coordinate_prob,repetition,sameExcept,valueDiscrete,valueFinite,valueMeasurable,witness,witness_bound,witness_covariance,witness_flip_other,witness_flip_self,witness_mean_zero,witness_measurable,witness_memLp,witness_orthogonal,witness_projection_pointwise,witness_square,witness_variance_lower
neighborMeasurable | bind-only | none | coordinateLaw,nvm_measurable,valueMeasurable
valueMeasurable | bind-only | none | Model.casesOn,Model.mk.inj,Model.mk.injEq,Model.mk.noConfusion,Model.mk.sizeOf_spec,Model.noConfusion,Model.noConfusionType,Model.recOn,W_measurable,W_memLp,coordinateLaw,coordinateLaw.congr_simp,coordinateLawProbability,erased_measurable,extraRefresh_measurable,extraRefresh_prob,flipFresh_preserving,good_integral,good_measurable,integral_flip,model_W_map,model_W_variance,model_explicitBound,model_joint_law,nvm_measurable,product_explicitBound,refresh_coordinate_prob,valueDiscrete,witness_covariance,witness_mean_zero,witness_measurable,witness_memLp,witness_orthogonal,witness_variance_lower
valueDiscrete | bind-only | none | flipFresh_preserving
coordinateLaw | construction | none | Model.casesOn,Model.mk.inj,Model.mk.injEq,Model.mk.noConfusion,Model.mk.sizeOf_spec,Model.noConfusion,Model.noConfusionType,Model.recOn,W_memLp,coordinateLaw.congr_simp,coordinateLawProbability,extraRefresh_prob,flipFresh_preserving,good_integral,integral_flip,model_W_map,model_W_variance,model_explicitBound,model_joint_law,product_explicitBound,refresh_coordinate_prob,witness_covariance,witness_mean_zero,witness_memLp,witness_orthogonal,witness_variance_lower
Model | construction | none | Model.belowOne,Model.casesOn,Model.connected,Model.coordinate,Model.ctorIdx,Model.hasNeighbor,Model.independent,Model.laws,Model.measurable_coordinate,Model.mk.inj,Model.mk.injEq,Model.mk.noConfusion,Model.noConfusion,Model.noConfusionType,Model.positiveNoise,Model.probability,Model.recOn,Model.ε,claim,model_W_map,model_W_variance,model_explicitBound,model_joint_law,result
nvm | construction | none | W,W_bound,W_measurable,W_sample_eq,coefficient,good,good_bound,good_flip_pair,good_measurable,local_erasure,local_statistic_difference,nvm.eq_def,nvm_before_flip,nvm_measurable,nvm_sample_eq,repetition,witness_bound,witness_flip_other,witness_flip_self,witness_measurable,witness_projection_pointwise,witness_square,witness_variance_lower
W | construction | none | W_bound,W_memLp,claim,local_statistic_difference,model_W_map,model_W_variance,model_explicitBound,product_explicitBound,result,witness_covariance,witness_projection_pointwise
coordinateLawProbability | bind-only | none | W_memLp,extraRefresh_prob,flipFresh_preserving,good_integral,product_explicitBound,refresh_coordinate_prob,witness_covariance,witness_memLp,witness_orthogonal,witness_variance_lower
valueFinite | bind-only | none | flipFresh_preserving
flipValue | construction | none | flipFresh,flipFresh_preserving,nvm_before_flip
flipFresh | construction | none | erased_flip,flipFresh_involutive,flipFresh_preserving,flipFresh_sameExcept,good_flip_pair,good_integral,integral_flip,nvm_before_flip,witness_covariance,witness_flip_other,witness_flip_self,witness_mean_zero,witness_orthogonal,witness_projection_pointwise
fairBit_not_map | bind-only | none | flipFresh_preserving
flipFresh_preserving | bind-only | none | good_integral,integral_flip,witness_covariance
sameExcept | construction | none | local_erasure,local_statistic_difference
flipFresh_sameExcept | bind-only | none | nvm_before_flip,witness_flip_other,witness_flip_self,witness_projection_pointwise
nvm_measurable | content | nvm_measurable | W_measurable,good_measurable,witness_measurable
W_measurable | content | nvm_measurable | W_memLp,model_W_map,model_W_variance
erased | construction | none | erased_flip,erased_measurable,extraRefresh,extraRefresh_measurable,good_flip_pair,local_erasure,local_statistic_difference,witness,witness_bound,witness_flip_other,witness_flip_self,witness_measurable,witness_orthogonal,witness_projection_pointwise,witness_square,witness_variance_lower
local_erasure | content | local_erasure | local_statistic_difference,witness_flip_other,witness_flip_self
repetition_spin | bind-only | none | local_statistic_difference
repetition | construction | none | W_bound,local_statistic_difference
local_statistic_difference | content | local_erasure | witness_projection_pointwise
centers | construction | none | center_bounds,centers_card,centers_no_lag,product_explicitBound,witness_orthogonal
centers_card | bind-only | none | product_explicitBound
center_bounds | bind-only | none | product_explicitBound,witness_orthogonal
centers_no_lag | bind-only | none | witness_orthogonal
incident_coefficient_square | bind-only | none | witness_square
orthogonal_variance_lower_bound | bind-only | none | product_explicitBound
flipFresh_involutive | bind-only | none | integral_flip
integral_flip | bind-only | none | good_integral,witness_covariance,witness_mean_zero,witness_orthogonal
erased_flip | bind-only | none | witness_flip_self
erased_measurable | bind-only | none | extraRefresh_measurable,witness_measurable
coefficient | construction | none | witness,witness_bound,witness_flip_other,witness_flip_self,witness_measurable,witness_orthogonal,witness_projection_pointwise,witness_square
witness | construction | none | product_explicitBound,witness_bound,witness_covariance,witness_flip_other,witness_flip_self,witness_mean_zero,witness_measurable,witness_memLp,witness_orthogonal,witness_projection_pointwise,witness_square,witness_variance_lower
witness_measurable | content | nvm_measurable | witness_memLp
witness_bound | bind-only | none | witness_memLp
W_bound | bind-only | none | W_memLp
witness_flip_self | content | local_erasure | witness_mean_zero,witness_orthogonal,witness_projection_pointwise
witness_projection_pointwise | content | local_erasure | witness_covariance
witness_memLp | content | nvm_measurable | product_explicitBound,witness_covariance,witness_orthogonal,witness_variance_lower
W_memLp | content | nvm_measurable | product_explicitBound,witness_covariance
witness_mean_zero | content | local_erasure | witness_covariance,witness_orthogonal,witness_variance_lower
witness_covariance | content | local_erasure | product_explicitBound
witness_flip_other | content | local_erasure | witness_orthogonal
witness_orthogonal | content | local_erasure | product_explicitBound
refreshSet | construction | none | extraRefresh_prob,refreshSet_card
refreshSet_card | bind-only | none | extraRefresh_prob
extraRefresh | construction | none | extraRefresh_prob,good,good_bound,good_flip_pair,good_integral,good_measurable,witness_variance_lower
extraRefresh_measurable | bind-only | none | good_integral,good_measurable
refresh_coordinate_prob | bind-only | none | extraRefresh_prob
extraRefresh_prob | bind-only | none | good_integral
nvm_before_flip | content | nvm_before_flip | good_flip_pair
good | construction | none | good_bound,good_flip_pair,good_integral,witness_variance_lower
good_measurable | content | nvm_measurable | good_integral,witness_variance_lower
good_bound | bind-only | none | good_integral,witness_variance_lower
good_flip_pair | content | nvm_before_flip | good_integral
good_integral | content | nvm_before_flip | witness_variance_lower
witness_square | bind-only | none | witness_variance_lower
witness_variance_lower | content | nvm_before_flip | product_explicitBound
product_explicitBound | content | local_erasure | model_explicitBound
model_joint_law | bind-only | none | model_W_map
nvm_sample_eq | content | nvm_sample_eq | W_sample_eq
W_sample_eq | content | nvm_sample_eq | model_W_map
model_W_map | content | nvm_sample_eq | model_W_variance
model_W_variance | content | nvm_sample_eq | model_explicitBound
not_littleO_of_floor_linear_lower_bound | bind-only | none | result
model_explicitBound | content | local_erasure | result
claim | construction | none | type-level construction
result | content | local_erasure | terminal result
-/

import D5.S3.Combinatorics.IsingUniquenessSets
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory Filter
open D5.S3.Combinatorics.IsingUniquenessSets (sgn)
open scoped BigOperators ENNReal

namespace D5.S3.StatisticalMechanics.NoisyVoter.RepetitionVarianceLinear

inductive Coord (V : Type*)
  | initial : V → Coord V
  | fresh : ℕ → V → Coord V
  | refresh : ℕ → V → Coord V
  | choice : ℕ → V → Coord V
  deriving DecidableEq

variable {V Ω : Type} (G : SimpleGraph V) [G.LocallyFinite]

abbrev Value : Coord V → Type
  | .initial _ => Bool
  | .fresh _ _ => Bool
  | .refresh _ _ => Bool
  | .choice _ v => ↥(G.neighborSet v)

private instance neighborMeasurable (v : V) : MeasurableSpace ↥(G.neighborSet v) := ⊤
private instance valueMeasurable : (i : Coord V) → MeasurableSpace (Value G i)
  | .initial _ => Bool.instMeasurableSpace
  | .fresh _ _ => Bool.instMeasurableSpace
  | .refresh _ _ => Bool.instMeasurableSpace
  | .choice _ v => neighborMeasurable G v
private instance valueDiscrete : (i : Coord V) → MeasurableSingletonClass (Value G i)
  | .initial _ => Bool.instMeasurableSingletonClass
  | .fresh _ _ => Bool.instMeasurableSingletonClass
  | .refresh _ _ => Bool.instMeasurableSingletonClass
  | .choice _ v => by
      change @MeasurableSingletonClass (G.neighborSet v) ⊤
      infer_instance

noncomputable def coordinateLaw (ε : unitInterval) (hNbr : ∀ v, ∃ w, G.Adj v w) :
    (i : Coord V) → Measure (Value G i)
  | .initial _ => (bernoulliMeasure true false (⟨1/2, by norm_num, by norm_num⟩ : unitInterval))
  | .fresh _ _ => (bernoulliMeasure true false (⟨1/2, by norm_num, by norm_num⟩ : unitInterval))
  | .refresh _ _ => bernoulliMeasure true false ε
  | .choice _ v => by
      letI : Nonempty (G.neighborSet v) := ⟨⟨(hNbr v).choose, (hNbr v).choose_spec⟩⟩
      let α := G.neighborSet v
      let p : PMF α := PMF.ofFintype (fun _ => (Fintype.card α : ℝ≥0∞)⁻¹) (by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
          (ENNReal.natCast_ne_top _))
      exact p.toMeasure

structure Model [MeasurableSpace Ω] (P : Measure Ω) where
  probability : IsProbabilityMeasure P
  connected : G.Connected
  hasNeighbor : ∀ v, ∃ w, G.Adj v w
  ε : unitInterval
  positiveNoise : 0 < (ε : ℝ)
  belowOne : (ε : ℝ) < 1
  coordinate : (i : Coord V) → Ω → Value G i
  measurable_coordinate : ∀ i, Measurable (coordinate i)
  independent : iIndepFun coordinate P
  laws : ∀ i, HasLaw (coordinate i) (coordinateLaw G ε hasNeighbor i) P

variable {G}

def nvm (x : (i : Coord V) → Ω → Value G i) : ℕ → V → Ω → Bool
  | 0, v, ω => x (.initial v) ω
  | t+1, v, ω => if x (.refresh (t+1) v) ω then x (.fresh (t+1) v) ω
      else nvm x t ((x (.choice (t+1) v) ω).val) ω

noncomputable def W (x : (i : Coord V) → Ω → Value G i) (u : V) (d t : ℕ) : Ω → ℝ :=
  fun ω => ∑ i ∈ Finset.Icc 1 t, (if nvm x i u ω = nvm x (i+d) u ω then 1 else 0 : ℝ)

private instance coordinateLawProbability (ε : unitInterval) (hNbr : ∀ v, ∃ w, G.Adj v w)
    (i : Coord V) : IsProbabilityMeasure (coordinateLaw G ε hNbr i) := by
  cases i with
  | initial v => exact instIsProbabilityMeasureBernoulliMeasure
  | fresh t v => exact instIsProbabilityMeasureBernoulliMeasure
  | refresh t v => exact instIsProbabilityMeasureBernoulliMeasure
  | choice t v =>
      unfold coordinateLaw
      dsimp
      infer_instance

private instance valueFinite (i : Coord V) : Finite (Value G i) := by
  cases i <;> dsimp [Value] <;> infer_instance

private noncomputable def flipValue (r : ℕ) (u : V) (i : Coord V) : Value G i → Value G i := by
  classical
  exact Function.update (fun j => (id : Value G j → Value G j)) (.fresh r u) Bool.not i

private noncomputable def flipFresh (r : ℕ) (u : V) (x : ((i : Coord V) → Value G i)) :
    ((i : Coord V) → Value G i) :=
  Pi.map (flipValue r u) x

private theorem fairBit_not_map :
    (bernoulliMeasure true false (⟨1/2, by norm_num, by norm_num⟩ : unitInterval)).map Bool.not =
      bernoulliMeasure true false (⟨1/2, by norm_num, by norm_num⟩ : unitInterval) := by
  rw [map_bernoulliMeasure]
  simp only [Bool.not_true, Bool.not_false]
  unfold bernoulliMeasure
  norm_num [unitInterval.toNNReal]
  exact add_comm _ _

private theorem flipFresh_preserving (ε : unitInterval) (hNbr : ∀ v, ∃ w, G.Adj v w)
    (r : ℕ) (u : V) : MeasurePreserving (flipFresh r u)
      (Measure.infinitePi (coordinateLaw G ε hNbr))
      (Measure.infinitePi (coordinateLaw G ε hNbr)) := by
  classical
  constructor
  · exact measurable_pi_iff.mpr (fun i =>
      (measurable_of_finite (flipValue r u i)).comp (measurable_pi_apply i))
  · unfold flipFresh Pi.map
    rw [Measure.infinitePi_map_pi (coordinateLaw G ε hNbr)
      (fun i => measurable_of_finite (flipValue r u i))]
    congr 1
    funext i
    by_cases h : i = .fresh r u
    · subst i
      simpa only [flipValue, Function.update_self, coordinateLaw] using fairBit_not_map
    · simp only [flipValue, Function.update_of_ne h, Measure.map_id]

private def sameExcept (x y : ((i : Coord V) → Value G i)) (r : ℕ) (u : V) : Prop :=
  ∀ i, i ≠ Coord.fresh r u → x i = y i

omit [G.LocallyFinite] in
private theorem flipFresh_sameExcept (x : ((i : Coord V) → Value G i)) (r : ℕ) (u : V) :
    sameExcept x (flipFresh r u x) r u := by
  intro i hi
  simp [flipFresh, Pi.map, flipValue, hi]

theorem nvm_measurable [MeasurableSpace Ω]
    (x : (i : Coord V) → Ω → Value G i) (hx : ∀ i, Measurable (x i)) :
    ∀ t v, Measurable (nvm x t v) := by
  intro t
  induction t with
  | zero => intro v; exact hx (.initial v)
  | succ t ih =>
    intro v
    have hcopy : Measurable (fun ω => nvm x t ((x (.choice (t+1) v) ω).val) ω) := by
      have hpair : Measurable (fun p : (G.neighborSet v) × Ω => nvm x t p.1.val p.2) :=
        measurable_from_prod_countable_right (fun w => ih w.val)
      exact hpair.comp ((hx (.choice (t+1) v)).prodMk measurable_id)
    exact Measurable.ite ((hx (.refresh (t+1) v)) (measurableSet_singleton true))
      (hx (.fresh (t+1) v)) hcopy

private theorem W_measurable [MeasurableSpace Ω]
    (x : (i : Coord V) → Ω → Value G i) (hx : ∀ i, Measurable (x i))
    (u : V) (d t : ℕ) : Measurable (W x u d t) := by
  classical
  apply Finset.measurable_sum
  intro i hi
  exact Measurable.ite (measurableSet_eq_fun (nvm_measurable x hx i u)
    (nvm_measurable x hx (i+d) u)) measurable_const measurable_const

private def erased (x : ((i : Coord V) → Value G i)) (r : ℕ) (u : V) : Prop :=
  x (.refresh r u) = true ∧ ∀ v, G.Adj u v → x (.refresh (r+1) v) = true

omit [G.LocallyFinite] in
private theorem local_erasure (x y : ((i : Coord V) → Value G i)) (r : ℕ) (u : V)
    (hxy : sameExcept x y r u) (hA : erased x r u) :
    ∀ s w, (s,w) ≠ (r,u) → nvm (fun i ω => ω i) s w x = nvm (fun i ω => ω i) s w y := by
  classical
  intro s
  induction s with
  | zero =>
    intro w hsw
    exact hxy (.initial w) (by simp)
  | succ s ih =>
    intro w hsw
    have hξ : x (.refresh (s+1) w) = y (.refresh (s+1) w) := hxy _ (by simp)
    have hη : x (.choice (s+1) w) = y (.choice (s+1) w) := hxy _ (by simp)
    have hY : x (.fresh (s+1) w) = y (.fresh (s+1) w) := by
      apply hxy
      intro heq
      have h := Coord.fresh.inj heq
      apply hsw
      exact Prod.ext h.1 h.2
    simp only [nvm]
    rw [← hξ, ← hη]
    by_cases hξt : x (.refresh (s+1) w) = true
    · simp [hξt, hY]
    · simp only [hξt]
      apply ih
      intro hp
      have hs : s = r := (Prod.mk.inj hp).1
      have hw : (x (.choice (s+1) w)).val = u := (Prod.mk.inj hp).2
      have hadj : G.Adj u w := (hw ▸ (x (.choice (s+1) w)).property).symm
      have : x (.refresh (s+1) w) = true := hs ▸ hA.2 w hadj
      simp_all

private theorem repetition_spin (a b : Bool) :
    (if a = b then 1 else 0 : ℝ) = (1 + sgn a * sgn b) / 2 := by
  cases a <;> cases b <;> norm_num [sgn]

private def repetition (x : ((i : Coord V) → Value G i)) (u : V) (d i : ℕ) : ℝ :=
  if nvm (fun i ω => ω i) i u x = nvm (fun i ω => ω i) (i+d) u x then 1 else 0

omit [G.LocallyFinite] in
private theorem local_statistic_difference (x y : ((i : Coord V) → Value G i))
    (r : ℕ) (u : V) (d t : ℕ)
    (hd : 1 ≤ d) (hdr : d < r) (hrt : r ≤ t)
    (hxy : sameExcept x y r u) (hA : erased x r u) :
    W (fun i ω => ω i) u d t x - W (fun i ω => ω i) u d t y =
      ((sgn (nvm (fun i ω => ω i) (r-d) u x) +
        sgn (nvm (fun i ω => ω i) (r+d) u x)) / 2) *
        (sgn (x (.fresh r u)) - sgn (y (.fresh r u))) := by
  classical
  have hleft : 1 ≤ r-d := Nat.le_sub_of_add_le' hdr
  have hrne : r-d ≠ r := by omega
  have hrmem : r ∈ Finset.Icc 1 t := Finset.mem_Icc.mpr ⟨by omega, hrt⟩
  have hlmem : r-d ∈ (Finset.Icc 1 t).erase r := by simp; omega
  have hrxi := hA.1
  have hyxi : y (.refresh r u) = true := (hxy (.refresh r u) (by simp)).symm.trans hrxi
  have hrootx : nvm (fun i ω => ω i) r u x = x (.fresh r u) := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    subst r
    simp [nvm, hrxi]
  have hrooty : nvm (fun i ω => ω i) r u y = y (.fresh r u) := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    subst r
    simp [nvm, hyxi]
  have heq := local_erasure x y r u hxy hA
  have hleftop : nvm (fun i ω => ω i) (r-d) u x = nvm (fun i ω => ω i) (r-d) u y :=
    heq _ _ (by intro h; have := (Prod.mk.inj h).1; omega)
  have hrightop : nvm (fun i ω => ω i) (r+d) u x = nvm (fun i ω => ω i) (r+d) u y :=
    heq _ _ (by intro h; have := (Prod.mk.inj h).1; omega)
  have hz : ∑ i ∈ ((Finset.Icc 1 t).erase r).erase (r-d),
      (repetition x u d i - repetition y u d i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hiR : i ≠ r := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    have hiL : i ≠ r-d := Finset.ne_of_mem_erase hi
    have hin : i+d ≠ r := by omega
    unfold repetition
    rw [heq i u (by simp [hiR]), heq (i+d) u (by simp [hin]), sub_self]
  change (∑ i ∈ Finset.Icc 1 t, repetition x u d i) -
    (∑ i ∈ Finset.Icc 1 t, repetition y u d i) = _
  rw [← Finset.sum_sub_distrib, ← Finset.sum_erase_add _ _ hrmem,
    ← Finset.sum_erase_add _ _ hlmem, hz, zero_add]
  simp only [repetition, repetition_spin]
  rw [show r-d+d = r by omega, hrootx, hrooty, ← hleftop, ← hrightop]
  ring

private def centers (d t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (t / (d+1))).image (fun k => k * (d+1))

private theorem centers_card (d t : ℕ) : (centers d t).card = t / (d+1) := by
  rw [centers, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos d) hab

private theorem center_bounds (d t r : ℕ) (hr : r ∈ centers d t) : d < r ∧ r ≤ t := by
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hr
  have hk' := Finset.mem_Icc.mp hk
  constructor
  · have hq : d+1 ≤ k*(d+1) := by
      simpa using Nat.mul_le_mul_right (d+1) hk'.1
    omega
  · calc k*(d+1) ≤ (t/(d+1))*(d+1) := Nat.mul_le_mul_right _ hk'.2
         _ ≤ t := Nat.div_mul_le_self _ _

private theorem centers_no_lag (d t r s : ℕ) (hd : 1 ≤ d)
    (hr : r ∈ centers d t) (hs : s ∈ centers d t) : r+d ≠ s := by
  have hmod : ∀ n ∈ centers d t, n % (d+1) = 0 := by
    intro n hn
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
    simp
  intro heq
  have hh := congrArg (fun n => n % (d+1)) heq
  rw [Nat.add_mod, hmod r hr, hmod s hs, zero_add,
    Nat.mod_eq_of_lt (Nat.lt_succ_self d), Nat.mod_eq_of_lt (Nat.lt_succ_self d)] at hh
  omega

private theorem incident_coefficient_square (a b : Bool) :
    ((sgn a + sgn b)/2)^2 = (if a = b then 1 else 0 : ℝ) := by
  cases a <;> cases b <;> norm_num [sgn]

private theorem orthogonal_variance_lower_bound [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {ι : Type*} (s : Finset ι)
    (W : Ω → ℝ) (Z : ι → Ω → ℝ)
    (hW : MemLp W 2 P) (hZ : ∀ i ∈ s, MemLp (Z i) 2 P)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → covariance (Z i) (Z j) P = 0)
    (hproj : ∀ i ∈ s, covariance W (Z i) P = variance (Z i) P) :
    (∑ i ∈ s, variance (Z i) P) ≤ variance W P := by
  classical
  let S : Ω → ℝ := ∑ i ∈ s, Z i
  have hS : MemLp S 2 P := memLp_finsetSum' s hZ
  have hvS : variance S P = ∑ i ∈ s, variance (Z i) P := by
    rw [variance_sum' hZ]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single_of_mem i hi]
    · exact covariance_self (hZ i hi).aemeasurable
    · intro j hj hji
      exact horth i hi j hj (Ne.symm hji)
  have hcS : covariance W S P = ∑ i ∈ s, variance (Z i) P := by
    rw [covariance_sum_right' hZ hW]
    exact Finset.sum_congr rfl (fun i hi => hproj i hi)
  have hv := variance_sub hW hS
  have hn := variance_nonneg (W - S) P
  rw [hv, hvS, hcS] at hn
  linarith


omit [G.LocallyFinite] in
private theorem flipFresh_involutive (r : ℕ) (u : V) :
    Function.Involutive (flipFresh (G := G) r u) := by
  classical
  intro x
  funext i
  by_cases h : i = .fresh r u
  · subst i; simp [flipFresh, Pi.map, flipValue]
  · simp [flipFresh, Pi.map, flipValue, h]

private theorem integral_flip (ε : unitInterval) (hNbr : ∀ v, ∃ w, G.Adj v w)
    (r : ℕ) (u : V) (f : ((i : Coord V) → Value G i) → ℝ) :
    (∫ x, f (flipFresh r u x) ∂(Measure.infinitePi (coordinateLaw G ε hNbr))) =
      ∫ x, f x ∂(Measure.infinitePi (coordinateLaw G ε hNbr)) :=
  (flipFresh_preserving ε hNbr r u).integral_comp
    (MeasurableEquiv.ofInvolutive (flipFresh r u) (flipFresh_involutive r u)
    (flipFresh_preserving ε hNbr r u).measurable).measurableEmbedding f

omit [G.LocallyFinite] in
private theorem erased_flip (x : ((i : Coord V) → Value G i)) (r s : ℕ) (u v : V) :
    erased (flipFresh r u x) s v ↔ erased x s v := by
  classical
  simp [erased, flipFresh, flipValue]

private theorem erased_measurable (r : ℕ) (u : V) :
    MeasurableSet {x : ((i : Coord V) → Value G i) | erased x r u} := by
  have heq : {x : ((i : Coord V) → Value G i) | erased x r u} =
      {x | x (.refresh r u) = true} ∩
      ⋂ v : G.neighborSet u, {x | x (.refresh (r+1) v.val) = true} := by
    ext x
    simp only [Set.mem_ofPred_eq, erased, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro h; exact ⟨h.1, fun v => h.2 v.val v.property⟩
    · intro h; exact ⟨h.1, fun v hv => h.2 ⟨v,hv⟩⟩
  rw [heq]
  have hcoord : ∀ k v,
      MeasurableSet {x : ((i : Coord V) → Value G i) | x (.refresh k v) = true} := by
    intro k v
    exact (measurable_pi_apply (Coord.refresh k v) :
      Measurable (fun x : ((i : Coord V) → Value G i) => x (Coord.refresh k v)))
      (show MeasurableSet ({true} : Set Bool) from measurableSet_singleton true)
  exact (hcoord r u).inter (MeasurableSet.iInter fun v => hcoord (r+1) v.val)

private noncomputable def coefficient (u : V) (d r : ℕ) (x : ((i : Coord V) → Value G i)) : ℝ :=
  (sgn (nvm (fun i ω => ω i) (r-d) u x) +
    sgn (nvm (fun i ω => ω i) (r+d) u x)) / 2

private noncomputable def witness (u : V) (d r : ℕ) (x : ((i : Coord V) → Value G i)) : ℝ :=
  by
    classical
    exact if erased x r u then coefficient u d r x * sgn (x (.fresh r u)) else 0

private theorem witness_measurable (u : V) (d r : ℕ) : Measurable (witness (G := G) u d r) := by
  unfold witness coefficient
  apply Measurable.ite (erased_measurable r u) _ measurable_const
  apply Measurable.mul
  · exact ((measurable_of_finite sgn).comp
      (nvm_measurable _ (fun i => measurable_pi_apply i) _ _)).add
      ((measurable_of_finite sgn).comp
      (nvm_measurable _ (fun i => measurable_pi_apply i) _ _)) |>.div_const 2
  · exact (measurable_of_finite sgn).comp (measurable_pi_apply _)

omit [G.LocallyFinite] in
private theorem witness_bound (u : V) (d r : ℕ) (x : ((i : Coord V) → Value G i)) :
    ‖witness u d r x‖ ≤ 1 := by
  classical
  unfold witness coefficient
  split_ifs
  · cases nvm (fun i ω => ω i) (r-d) u x <;>
      cases nvm (fun i ω => ω i) (r+d) u x <;>
      cases x (.fresh r u) <;> norm_num [sgn]
  · norm_num

omit [G.LocallyFinite] in
private theorem W_bound (u : V) (d t : ℕ) (x : ((i : Coord V) → Value G i)) :
    ‖W (fun i ω => ω i) u d t x‖ ≤ (t : ℝ) := by
  classical
  change ‖∑ i ∈ Finset.Icc 1 t, repetition x u d i‖ ≤ (t : ℝ)
  calc ‖∑ i ∈ Finset.Icc 1 t, repetition x u d i‖
      ≤ ∑ i ∈ Finset.Icc 1 t, ‖repetition x u d i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.Icc 1 t, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      unfold repetition
      split_ifs <;> norm_num
    _ = (t : ℝ) := by simp

omit [G.LocallyFinite] in
private theorem witness_flip_self (x : ((i : Coord V) → Value G i)) (r : ℕ) (u : V) (d : ℕ)
    (hd : 1 ≤ d) (hdr : d < r) :
    witness u d r (flipFresh r u x) = - witness u d r x := by
  classical
  have hA := erased_flip x r r u u
  by_cases ha : erased x r u
  · have he := local_erasure x (flipFresh r u x) r u
      (flipFresh_sameExcept x r u) ha
    have hl := he (r-d) u (by intro h; have := (Prod.mk.inj h).1; omega)
    have hh := he (r+d) u (by intro h; have := (Prod.mk.inj h).1; omega)
    have hs : sgn ((flipFresh r u x) (.fresh r u)) = - sgn (x (.fresh r u)) := by
      simp only [flipFresh, Pi.map, flipValue, Function.update_self]
      exact D5.S3.Combinatorics.IsingUniquenessSets.sgn_not _
    simp only [witness, hA.mpr ha, ha, ↓reduceIte, coefficient, ← hl, ← hh, hs]
    ring
  · simp [witness, ha, hA]

omit [G.LocallyFinite] in
private theorem witness_projection_pointwise (x : ((i : Coord V) → Value G i))
    (r : ℕ) (u : V) (d t : ℕ)
    (hd : 1 ≤ d) (hdr : d < r) (hrt : r ≤ t) :
    W (fun i ω => ω i) u d t x * witness u d r x +
      W (fun i ω => ω i) u d t (flipFresh r u x) *
        witness u d r (flipFresh r u x) = 2 * (witness u d r x)^2 := by
  classical
  rw [witness_flip_self x r u d hd hdr]
  by_cases hA : erased x r u
  · have hh := local_statistic_difference x (flipFresh r u x) r u d t hd hdr hrt
      (flipFresh_sameExcept x r u) hA
    have hs : sgn ((flipFresh r u x) (.fresh r u)) = - sgn (x (.fresh r u)) := by
      simp only [flipFresh, Pi.map, flipValue, Function.update_self]
      exact D5.S3.Combinatorics.IsingUniquenessSets.sgn_not _
    change _ = coefficient u d r x * _ at hh
    rw [hs] at hh
    simp only [witness, hA, ↓reduceIte]
    have hm := congrArg (fun z : ℝ => z * (coefficient u d r x * sgn (x (.fresh r u)))) hh
    nlinarith [hm]
  · simp [witness, hA]


private theorem witness_memLp (ε : unitInterval) (hNbr : ∀ v, ∃ w, G.Adj v w)
    (u : V) (d r : ℕ) : MemLp (witness u d r) 2 ((Measure.infinitePi (coordinateLaw G ε hNbr))) :=
  MemLp.of_bound (witness_measurable u d r).aestronglyMeasurable 1
    (Eventually.of_forall (witness_bound u d r))

private theorem W_memLp (ε : unitInterval) (hNbr : ∀ v, ∃ w, G.Adj v w)
    (u : V) (d t : ℕ) :
    MemLp (W (fun i ω => ω i) u d t) 2 (Measure.infinitePi (coordinateLaw G ε hNbr)) :=
  MemLp.of_bound (W_measurable _ (fun i => measurable_pi_apply i) u d t).aestronglyMeasurable
    t (Eventually.of_forall (W_bound u d t))

private theorem witness_mean_zero (ε : unitInterval) (hNbr : ∀ v, ∃ w, G.Adj v w)
    (u : V) (d r : ℕ) (hd : 1 ≤ d) (hdr : d < r) :
    (∫ x, witness u d r x ∂(Measure.infinitePi (coordinateLaw G ε hNbr))) = 0 := by
  have h := integral_flip ε hNbr r u (witness u d r)
  simp_rw [witness_flip_self _ r u d hd hdr, integral_neg] at h
  linarith

private theorem witness_covariance (ε : unitInterval) (hNbr : ∀ v, ∃ w, G.Adj v w)
    (u : V) (d r t : ℕ) (hd : 1 ≤ d) (hdr : d < r) (hrt : r ≤ t) :
    covariance (W (fun i ω => ω i) u d t) (witness u d r)
        (Measure.infinitePi (coordinateLaw G ε hNbr)) =
      variance (witness u d r) ((Measure.infinitePi (coordinateLaw G ε hNbr))) := by
  let μ := (Measure.infinitePi (coordinateLaw G ε hNbr))
  have hW := W_memLp ε hNbr u d t
  have hZ := witness_memLp ε hNbr u d r
  have hflip := flipFresh_preserving ε hNbr r u
  have hp := integral_congr_ae (μ := μ) (Eventually.of_forall
    (fun x => witness_projection_pointwise x r u d t hd hdr hrt))
  have hg : Integrable (fun x => W (fun i ω => ω i) u d t x * witness u d r x) μ :=
    hW.integrable_mul hZ
  have hgf : Integrable (fun x => W (fun i ω => ω i) u d t (flipFresh r u x) *
      witness u d r (flipFresh r u x)) μ :=
    (hW.comp_measurePreserving hflip).integrable_mul (hZ.comp_measurePreserving hflip)
  rw [integral_add hg hgf, integral_const_mul] at hp
  rw [integral_flip ε hNbr r u (fun x => W (fun i ω => ω i) u d t x * witness u d r x)] at hp
  rw [covariance_eq_sub hW hZ, variance_eq_sub hZ,
    witness_mean_zero ε hNbr u d r hd hdr]
  change (∫ x, W (fun i ω => ω i) u d t x * witness u d r x ∂μ) - _ =
    (∫ x, (witness u d r x)^2 ∂μ) - _
  simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero]
  linarith

omit [G.LocallyFinite] in
private theorem witness_flip_other (x : ((i : Coord V) → Value G i)) (u : V) (d r s : ℕ)
    (_hdr : d < r) (hrs : r ≠ s) (hl : s - d ≠ r) (hh : s + d ≠ r)
    (hA : erased x r u) : witness u d s (flipFresh r u x) = witness u d s x := by
  classical
  have he := local_erasure x (flipFresh r u x) r u
    (flipFresh_sameExcept x r u) hA
  have hleft := he (s-d) u (by simp [hl])
  have hright := he (s+d) u (by simp [hh])
  have hy : (flipFresh r u x) (.fresh s u) = x (.fresh s u) := by
    simp [flipFresh, Pi.map, flipValue, Ne.symm hrs]
  simp only [witness, erased_flip, coefficient, ← hleft, ← hright, hy]

private theorem witness_orthogonal (ε : unitInterval) (hNbr : ∀ v, ∃ w, G.Adj v w)
    (u : V) (d t r s : ℕ) (hd : 1 ≤ d)
    (hr : r ∈ centers d t) (hs : s ∈ centers d t) (hrs : r ≠ s) :
    covariance (witness u d r) (witness u d s)
      (Measure.infinitePi (coordinateLaw G ε hNbr)) = 0 := by
  classical
  have hbr := center_bounds d t r hr
  have hbs := center_bounds d t s hs
  have hl : s-d ≠ r := by
    intro h
    apply centers_no_lag d t r s hd hr hs
    omega
  have hh : s+d ≠ r := centers_no_lag d t s r hd hs hr
  have hp : ∀ x : ((i : Coord V) → Value G i),
      witness u d r (flipFresh r u x) * witness u d s (flipFresh r u x) =
        -(witness u d r x * witness u d s x) := by
    intro x
    rw [witness_flip_self x r u d hd hbr.1]
    by_cases hA : erased x r u
    · rw [witness_flip_other x u d r s hbr.1 hrs hl hh hA]
      ring
    · simp [witness, hA]
  have hi := integral_flip ε hNbr r u (fun x => witness u d r x * witness u d s x)
  simp_rw [hp, integral_neg] at hi
  rw [covariance_eq_sub (witness_memLp ε hNbr u d r) (witness_memLp ε hNbr u d s),
    witness_mean_zero ε hNbr u d r hd hbr.1]
  change (∫ x, witness u d r x * witness u d s x
    ∂(Measure.infinitePi (coordinateLaw G ε hNbr))) - _ = 0
  simp only [zero_mul, sub_zero]
  linarith

private noncomputable def refreshSet (u : V) (d r : ℕ) : Finset (ℕ × V) := by
  classical
  exact insert (r,u) (insert (r+d,u) ((G.neighborFinset u).image (fun v => (r+1,v))))

private theorem refreshSet_card (u : V) (d r : ℕ) (hd : 1 ≤ d) :
    (refreshSet (G := G) u d r).card = G.degree u + 2 := by
  classical
  have hi : Function.Injective (fun v : V => (r+1,v)) := by
    exact Prod.mk_right_injective (r+1)
  have hnon : ∀ k, (k,u) ∉ (G.neighborFinset u).image (fun v => (r+1,v)) := by
    intro k
    simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
    rintro ⟨v,hv,h⟩
    have hvu := (Prod.mk.inj h).2
    subst v
    exact G.irrefl hv
  unfold refreshSet
  rw [Finset.card_insert_of_notMem (by simp [hnon]; omega),
    Finset.card_insert_of_notMem (hnon _), Finset.card_image_of_injective _ hi]
  simp only [SimpleGraph.card_neighborFinset_eq_degree]

private def extraRefresh (u : V) (d r : ℕ) (x : ((i : Coord V) → Value G i)) : Prop :=
  erased x r u ∧ x (.refresh (r+d) u) = true

private theorem extraRefresh_measurable (u : V) (d r : ℕ) :
    MeasurableSet {x : ((i : Coord V) → Value G i) | extraRefresh u d r x} := by
  exact (erased_measurable r u).inter
    ((measurable_pi_apply (Coord.refresh (r+d) u) : Measurable
      (fun x : ((i : Coord V) → Value G i) => x (Coord.refresh (r+d) u)))
      (measurableSet_singleton true))

private theorem refresh_coordinate_prob (ε : unitInterval) (hNbr : ∀ v, ∃ w, G.Adj v w)
    (p : ℕ × V) :
    (Measure.infinitePi (coordinateLaw G ε hNbr))
        {x : ((i : Coord V) → Value G i) | x (.refresh p.1 p.2) = true} =
      (unitInterval.toNNReal ε : ℝ≥0∞) := by
  have hm := Measure.infinitePi_map_eval (coordinateLaw G ε hNbr) (.refresh p.1 p.2)
  have he := congrArg (fun ν : Measure Bool => ν {true}) hm
  rw [Measure.map_apply (show Measurable
    (fun x : ((i : Coord V) → Value G i) => x (Coord.refresh p.1 p.2))
    from measurable_pi_apply _) (measurableSet_singleton true)] at he
  simpa [coordinateLaw, bernoulliMeasure_apply, Set.preimage] using he

private theorem extraRefresh_prob (ε : unitInterval) (hNbr : ∀ v, ∃ w, G.Adj v w)
    (u : V) (d r : ℕ) (hd : 1 ≤ d) :
    (Measure.infinitePi (coordinateLaw G ε hNbr)).real
        {x : ((i : Coord V) → Value G i) | extraRefresh u d r x} =
      (ε : ℝ) ^ (G.degree u + 2) := by
  classical
  have hi : Function.Injective (fun p : ℕ × V => Coord.refresh p.1 p.2) := by
    intro a b h
    have hh := Coord.refresh.inj h
    exact Prod.ext hh.1 hh.2
  have hind := (iIndepFun_infinitePi (P := coordinateLaw G ε hNbr)
    (X := fun i a => a) (by fun_prop)).precomp hi
  have hp := hind.measure_inter_preimage_eq_mul (refreshSet (G := G) u d r)
    (sets := fun _ => ({true} : Set Bool)) (fun _ _ => measurableSet_singleton true)
  have heq : {x : ((i : Coord V) → Value G i) | extraRefresh u d r x} =
      ⋂ p ∈ refreshSet (G := G) u d r,
        {x : ((i : Coord V) → Value G i) | x (.refresh p.1 p.2) = true} := by
    ext x
    simp only [extraRefresh, erased, refreshSet, SimpleGraph.mem_neighborFinset,
      Set.mem_iInter, Finset.mem_insert, Finset.mem_image, Set.mem_ofPred_eq]
    simp only [forall_eq_or_imp, forall_exists_index, forall_and_index, forall_apply_eq_imp_iff₂]
    aesop
  change ((Measure.infinitePi (coordinateLaw G ε hNbr))) (⋂ p ∈ refreshSet (G := G) u d r,
    {x : ((i : Coord V) → Value G i) | x (.refresh p.1 p.2) = true}) =
      ∏ p ∈ refreshSet (G := G) u d r, ((Measure.infinitePi (coordinateLaw G ε hNbr)))
        {x : ((i : Coord V) → Value G i) | x (.refresh p.1 p.2) = true} at hp
  rw [← heq] at hp
  simp_rw [refresh_coordinate_prob ε hNbr] at hp
  rw [Finset.prod_const, refreshSet_card u d r hd] at hp
  unfold Measure.real
  rw [hp, ENNReal.toReal_pow]
  rw [ENNReal.coe_toReal]
  rfl

omit [G.LocallyFinite] in
private theorem nvm_before_flip (x : ((i : Coord V) → Value G i)) (r : ℕ) (u : V) :
    ∀ s, s < r → ∀ w,
      nvm (fun i ω => ω i) s w (flipFresh r u x) = nvm (fun i ω => ω i) s w x := by
  classical
  intro s
  induction s with
  | zero => intro hs w; simp [nvm, flipFresh, flipValue]
  | succ s ih =>
    intro hs w
    have hn : Coord.fresh (s+1) w ≠ Coord.fresh r u := by
      intro h; have := (Coord.fresh.inj h).1; omega
    simp only [nvm]
    have hξ : (flipFresh r u x) (.refresh (s+1) w) = x (.refresh (s+1) w) :=
      Bool.le_antisymm (fun a => a) (congrArg (flipValue r u (Coord.refresh (s+1) w)))
    have hη : (flipFresh r u x) (.choice (s+1) w) = x (.choice (s+1) w) :=
      SetCoe.ext rfl
    have hY : (flipFresh r u x) (.fresh (s+1) w) = x (.fresh (s+1) w) :=
      (flipFresh_sameExcept x r u _ hn).symm
    rw [hξ, hη, hY]
    split_ifs
    · rfl
    · exact ih (by omega) _

private noncomputable def good (u : V) (d r : ℕ) (x : ((i : Coord V) → Value G i)) : ℝ := by
  classical
  exact if extraRefresh u d r x ∧
    nvm (fun i ω => ω i) (r-d) u x = nvm (fun i ω => ω i) (r+d) u x then 1 else 0

private theorem good_measurable (u : V) (d r : ℕ) : Measurable (good (G := G) u d r) := by
  classical
  exact Measurable.ite ((extraRefresh_measurable u d r).inter
    (measurableSet_eq_fun (nvm_measurable _ (fun i => measurable_pi_apply i) _ _)
      (nvm_measurable _ (fun i => measurable_pi_apply i) _ _)))
    measurable_const measurable_const

omit [G.LocallyFinite] in
private theorem good_bound (u : V) (d r : ℕ) (x : ((i : Coord V) → Value G i)) :
    ‖good u d r x‖ ≤ 1 := by
  classical
  unfold good
  split_ifs <;> norm_num

open Classical in
omit [G.LocallyFinite] in
private theorem good_flip_pair (x : ((i : Coord V) → Value G i)) (u : V) (d r : ℕ) (hd : 1 ≤ d) :
    good u d r x + good u d r (flipFresh (r+d) u x) =
      (if extraRefresh u d r x then 1 else 0 : ℝ) := by
  classical
  have ha : extraRefresh u d r (flipFresh (r+d) u x) ↔ extraRefresh u d r x := by
    exact Eq.to_iff rfl
  by_cases hA : extraRefresh u d r x
  · have hξ := hA.2
    have hroot : nvm (fun i ω => ω i) (r+d) u x = x (.fresh (r+d) u) := by
      obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r+d ≠ 0)
      rw [hk] at hξ ⊢
      simp [nvm, hξ]
    have hξ' : (flipFresh (r+d) u x) (.refresh (r+d) u) = true := by
      simpa [flipFresh, Pi.map, flipValue] using hξ
    have hroot' : nvm (fun i ω => ω i) (r+d) u (flipFresh (r+d) u x) =
        !(x (.fresh (r+d) u)) := by
      obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r+d ≠ 0)
      rw [hk] at hξ' ⊢
      rw [nvm]
      simp only [hξ', ↓reduceIte]
      simp [flipFresh, Pi.map, flipValue]
    have hp := nvm_before_flip x (r+d) u (r-d) (by omega) u
    simp only [good, hA, ha.mpr hA, true_and, ↓reduceIte, hp, hroot, hroot']
    cases nvm (fun i ω => ω i) (r-d) u x <;>
      cases x (.fresh (r+d) u) <;> norm_num
  · simp [good, hA, ha]

private theorem good_integral (ε : unitInterval) (hNbr : ∀ v, ∃ w, G.Adj v w)
    (u : V) (d r : ℕ) (hd : 1 ≤ d) :
    (∫ x, good u d r x ∂(Measure.infinitePi (coordinateLaw G ε hNbr))) =
      (ε : ℝ) ^ (G.degree u + 2) / 2 := by
  classical
  let μ := (Measure.infinitePi (coordinateLaw G ε hNbr))
  have hg : MemLp (good u d r) 2 μ := MemLp.of_bound
    (good_measurable u d r).aestronglyMeasurable 1 (Eventually.of_forall (good_bound u d r))
  have hf := flipFresh_preserving ε hNbr (r+d) u
  have hp := integral_congr_ae (μ := μ) (Eventually.of_forall (fun x => good_flip_pair x u d r hd))
  rw [integral_add (show Integrable (fun x => good u d r x) μ from hg.integrable one_le_two)
      (show Integrable (fun x => good u d r (flipFresh (r+d) u x)) μ from
        (hg.comp_measurePreserving hf).integrable one_le_two),
    integral_flip ε hNbr (r+d) u] at hp
  have hi : (∫ x, (if extraRefresh u d r x then 1 else 0 : ℝ) ∂μ) =
      (ε : ℝ) ^ (G.degree u + 2) := by
    have he := integral_indicator_one (μ := μ) (extraRefresh_measurable u d r)
    have hreal := extraRefresh_prob ε hNbr u d r hd
    change μ.real {x | extraRefresh u d r x} = _ at hreal
    rw [← hreal]
    simpa [Set.indicator] using he
  rw [hi] at hp
  linarith

open Classical in
omit [G.LocallyFinite] in
private theorem witness_square (x : ((i : Coord V) → Value G i)) (u : V) (d r : ℕ) :
    (witness u d r x)^2 =
      (if erased x r u then
        (if nvm (fun i ω => ω i) (r-d) u x = nvm (fun i ω => ω i) (r+d) u x then 1 else 0)
      else 0 : ℝ) := by
  classical
  by_cases hA : erased x r u
  · simp only [witness, hA, ↓reduceIte, mul_pow, coefficient, incident_coefficient_square]
    cases x (.fresh r u) <;> norm_num [sgn]
  · simp [witness, hA]

private theorem witness_variance_lower (ε : unitInterval) (hNbr : ∀ v, ∃ w, G.Adj v w)
    (u : V) (d r : ℕ) (hd : 1 ≤ d) (hdr : d < r) :
    (ε : ℝ) ^ (G.degree u + 2) / 2 ≤
      variance (witness u d r) (Measure.infinitePi (coordinateLaw G ε hNbr)) := by
  classical
  let μ := (Measure.infinitePi (coordinateLaw G ε hNbr))
  have hZ := witness_memLp ε hNbr u d r
  have hg : MemLp (good u d r) 2 μ := MemLp.of_bound
    (good_measurable u d r).aestronglyMeasurable 1 (Eventually.of_forall (good_bound u d r))
  have hpoint : ∀ x : ((i : Coord V) → Value G i), good u d r x ≤ (witness u d r x)^2 := by
    intro x
    by_cases h : extraRefresh u d r x ∧
        nvm (fun i ω => ω i) (r-d) u x = nvm (fun i ω => ω i) (r+d) u x
    · rw [witness_square]
      simp [good, h, h.1.1]
    · simp only [good, h, ↓reduceIte]
      exact sq_nonneg _
  have hi := integral_mono (hg.integrable one_le_two) hZ.integrable_sq
    hpoint
  rw [good_integral ε hNbr u d r hd] at hi
  rw [variance_eq_sub hZ, witness_mean_zero ε hNbr u d r hd hdr]
  simpa only [Pi.pow_apply, zero_pow (by decide : 2 ≠ 0), sub_zero] using hi

private theorem product_explicitBound (ε : unitInterval) (hNbr : ∀ v, ∃ w, G.Adj v w)
    (u : V) (d : ℕ) (hd : 1 ≤ d) :
    ∀ t : ℕ, ((ε : ℝ) ^ (G.degree u + 2) / 2) * ((t / (d + 1) : ℕ) : ℝ) ≤
      variance (W (fun i x => x i) u d t) ((Measure.infinitePi (coordinateLaw G ε hNbr))) := by
  intro t
  have ho := orthogonal_variance_lower_bound (Measure.infinitePi (coordinateLaw G ε hNbr))
    (centers d t)
    (W (fun i x => x i) u d t) (witness u d)
    (W_memLp ε hNbr u d t) (fun r _ => witness_memLp ε hNbr u d r)
    (fun r hr s hs hrs => witness_orthogonal ε hNbr u d t r s hd hr hs hrs)
    (fun r hr => witness_covariance ε hNbr u d r t hd
      (center_bounds d t r hr).1 (center_bounds d t r hr).2)
  have hl : (∑ r ∈ centers d t, (ε : ℝ) ^ (G.degree u + 2) / 2) ≤
      ∑ r ∈ centers d t, variance (witness u d r) ((Measure.infinitePi (coordinateLaw G ε hNbr))) :=
    Finset.sum_le_sum (fun r hr => witness_variance_lower ε hNbr u d r hd
      (center_bounds d t r hr).1)
  have hh := hl.trans ho
  simpa only [Finset.sum_const, nsmul_eq_mul, centers_card, mul_comm] using hh

private theorem model_joint_law [MeasurableSpace Ω] (P : Measure Ω) (M : Model G P) :
    HasLaw (fun ω i => M.coordinate i ω)
      (Measure.infinitePi (coordinateLaw G M.ε M.hasNeighbor)) P := by
  exact M.independent.hasLaw_infinitePi M.laws
    (measurable_pi_iff.mpr M.measurable_coordinate).aemeasurable

omit [G.LocallyFinite] in
private theorem nvm_sample_eq (x : (i : Coord V) → Ω → Value G i) : ∀ t v ω,
    nvm (fun i y => y i) t v (fun i => x i ω) = nvm x t v ω := by
  intro t
  induction t with
  | zero => intro v ω; rfl
  | succ t ih =>
    intro v ω
    simp only [nvm]
    split_ifs <;> try rfl
    exact ih _ ω

omit [G.LocallyFinite] in
private theorem W_sample_eq (x : (i : Coord V) → Ω → Value G i) (u : V) (d t : ℕ) (ω : Ω) :
    W (fun i y => y i) u d t (fun i => x i ω) = W x u d t ω := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  rw [nvm_sample_eq, nvm_sample_eq]

private theorem model_W_map [MeasurableSpace Ω] (P : Measure Ω) (M : Model G P)
    (u : V) (d t : ℕ) :
    P.map (W M.coordinate u d t) =
      (Measure.infinitePi (coordinateLaw G M.ε M.hasNeighbor)).map
        (W (fun i y => y i) u d t) := by
  have hj := (model_joint_law P M).map_eq
  rw [← hj, Measure.map_map (W_measurable (Ω := ((i : Coord V) → Value G i)) (G := G)
    (fun i y => y i) (fun i => measurable_pi_apply i) u d t)
      (measurable_pi_iff.mpr M.measurable_coordinate)]
  congr 1
  funext ω
  exact (W_sample_eq M.coordinate u d t ω).symm

private theorem model_W_variance [MeasurableSpace Ω] (P : Measure Ω) (M : Model G P)
    (u : V) (d t : ℕ) :
    variance (W M.coordinate u d t) P =
      variance (W (fun i y => y i) u d t)
        (Measure.infinitePi (coordinateLaw G M.ε M.hasNeighbor)) := by
  rw [← variance_id_map (W_measurable M.coordinate M.measurable_coordinate u d t).aemeasurable,
      model_W_map P M u d t,
      variance_id_map (W_measurable (Ω := ((i : Coord V) → Value G i)) (G := G)
        (fun i y => y i) (fun i => measurable_pi_apply i) u d t).aemeasurable]

private theorem not_littleO_of_floor_linear_lower_bound (f : ℕ → ℝ) (c : ℝ) (q : ℕ)
    (hc : 0 < c) (hq : 0 < q) (hb : ∀ n, c * ((n / q : ℕ) : ℝ) ≤ f n) :
    ¬ f =o[atTop] (fun n => (n : ℝ)) := by
  intro h
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have he : 0 < c / (2 * (q : ℝ)) := div_pos hc (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.bound he)
  have hlarge : N ≤ (N+1)*q := by
    calc N ≤ N+1 := Nat.le_succ N
         _ ≤ (N+1)*q := Nat.le_mul_of_pos_right _ hq
  have hu := hN ((N+1)*q) hlarge
  have hl := hb ((N+1)*q)
  simp only [Nat.mul_div_left _ hq] at hl
  have hn : 0 < ((N+1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos N)
  have hnq : 0 ≤ (((N+1)*q : ℕ) : ℝ) := Nat.cast_nonneg _
  simp only [Real.norm_eq_abs] at hu
  rw [abs_of_nonneg hnq, Nat.cast_mul] at hu
  have hf : f ((N+1)*q) ≤ |f ((N+1)*q)| := le_abs_self _
  have heq : c / (2 * (q : ℝ)) * (((N+1 : ℕ) : ℝ) * q) = c * ((N+1 : ℕ) : ℝ) / 2 := by
    field_simp
  rw [heq] at hu
  nlinarith

private theorem model_explicitBound [MeasurableSpace Ω] (P : Measure Ω) (M : Model G P)
    (u : V) (d : ℕ) (hd : 1 ≤ d) :
    ∀ t : ℕ, ((M.ε : ℝ) ^ (G.degree u + 2) / 2) * ((t / (d + 1) : ℕ) : ℝ) ≤
      variance (W M.coordinate u d t) P := by
  intro t
  rw [model_W_variance P M u d t]
  exact product_explicitBound M.ε M.hasNeighbor u d hd t

def claim : Prop :=
  ∀ (V : Type) [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (M : Model G P) (u : V) (d : ℕ),
    1 ≤ d → ¬ (fun t : ℕ => variance (W M.coordinate u d t) P) =o[atTop]
      (fun t => (t : ℝ))

theorem result : claim := by
  intro V _ G _ Ω _ P M u d hd
  exact not_littleO_of_floor_linear_lower_bound _ _ _
    (div_pos (pow_pos M.positiveNoise _) (by norm_num)) (Nat.succ_pos d)
    (model_explicitBound P M u d hd)

end D5.S3.StatisticalMechanics.NoisyVoter.RepetitionVarianceLinear
