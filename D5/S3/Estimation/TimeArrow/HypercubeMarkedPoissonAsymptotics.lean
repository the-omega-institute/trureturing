/- GID: D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original hypercube asymptotics retain arbitrary integer times and uniform actual-law Poisson comparison. -/

import D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
import D5.S3.Estimation.TimeArrow.MarkedPoissonEventComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Batteries.Tactic.OpenPrivate

open Finset Filter MeasureTheory
open scoped Topology NNReal Classical
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra
open D5.S3.Estimation.TimeArrow.ActualReverseMarkedPath
open D5.S3.Estimation.TimeArrow.ArbitraryMarkedCountPoissonRelative
open D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
open D5.S3.Estimation.TimeArrow.MarkedPoissonEventComparison
open private forwardRates forward_rate_values markedVector poisson_product_singleton from
  D5.S3.Estimation.TimeArrow.MarkedPoissonEventComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Estimation.TimeArrow.HypercubeMarkedHistory

/-- A positive-dimensional original sign hypercube. -/
abbrev Cube (d : ℕ) := Fin (d + 1) → ℤˣ
private theorem sign_mul_self (u : ℤˣ) : u * u = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num
private def tailEnum (d : ℕ) : (Fin d → ℤˣ) ≃ Fin (2 ^ d) :=
  (Fintype.equivFin _).trans (finCongr (by simp [Fintype.card_fun, Fintype.card_units_int]))
private def signSplit : ℤˣ ≃ (Unit ⊕ Unit) where
  toFun u := if u = 1 then .inl () else .inr ()
  invFun z := match z with | .inl _ => 1 | .inr _ => -1
  left_inv u := by rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num
  right_inv z := by cases z <;> simp
private def parityCoordinates (d : ℕ) : Cube d ≃ ℤˣ × (Fin d → ℤˣ) where
  toFun x := (∏ i, x i, fun i => x i.succ)
  invFun z := Fin.cons (z.1 * ∏ i, z.2 i) z.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Fin.prod_univ_succ]
      rw [mul_assoc, sign_mul_self, mul_one]
    · simp
  right_inv z := by
    apply Prod.ext
    · simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [mul_assoc, sign_mul_self, mul_one]
    · funext i; simp
/-- The parity coordinate chooses the native class; the remaining coordinates index its states. -/
def cubeEquiv (d : ℕ) : Cube d ≃ Vertex (2 ^ d) :=
  (parityCoordinates d).trans
    ((Equiv.prodCongr signSplit (tailEnum d)).trans
      { toFun := fun z => match z.1 with | .inl _ => .inl z.2 | .inr _ => .inr z.2
        invFun := fun z => match z with | .inl i => (.inl (), i) | .inr i => (.inr (), i)
        left_inv := by rintro ⟨z, i⟩; cases z <;> rfl
        right_inv := by intro z; cases z <;> rfl })
private theorem cubeEquiv_parity (d : ℕ) (x : Cube d) :
    chi (cubeEquiv d x) = parity x := by
  have he : (∏ i, x i : ℤˣ) = 1 ∨ (∏ i, x i : ℤˣ) = -1 := Int.units_eq_one_or _
  rcases he with he | he <;>
    simp [cubeEquiv, parityCoordinates, signSplit, parity, chi, he]
/-- Every actual positive-parity cube state has exactly one native positive-state index. -/
def positiveEquiv (d : ℕ) : {x : Cube d // parity x = 1} ≃ Fin (2 ^ d) := by
  let f (i : Fin (2 ^ d)) : {x : Cube d // parity x = 1} :=
    ⟨(cubeEquiv d).symm (.inl i), by
      have h := cubeEquiv_parity d ((cubeEquiv d).symm (.inl i))
      simpa [chi] using h.symm⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      have he := congrArg (fun x : {x : Cube d // parity x = 1} => cubeEquiv d x.val) h
      simpa [f] using he
    · intro x
      cases he : cubeEquiv d x.val with
      | inl i =>
        refine ⟨i, Subtype.ext ?_⟩
        exact (cubeEquiv d).injective (by simpa [f] using he.symm)
      | inr i =>
        have hp := cubeEquiv_parity d x.val
        rw [he, chi, x.property] at hp
        norm_num at hp
  exact (Equiv.ofBijective f hf).symm
private theorem positiveEquiv_vertex (d : ℕ) (x : {x : Cube d // parity x = 1}) :
    cubeEquiv d x.val = .inl (positiveEquiv d x) := by
  have h := congrArg (fun y : {x : Cube d // parity x = 1} => cubeEquiv d y.val)
    ((positiveEquiv d).symm_apply_apply x)
  change cubeEquiv d ((cubeEquiv d).symm (.inl (positiveEquiv d x))) = cubeEquiv d x.val at h
  simpa only [Equiv.apply_symm_apply] using h.symm
/-- A source support is any q-element subset of the original positive parity class. -/
abbrev CubeSupport (d q : ℕ) :=
  {S : Finset {x : Cube d // parity x = 1} // S.card = q}
/-- This equivalence exhausts all original supports; no transport hypothesis is imposed. -/
def cubeSupportEquiv (d q : ℕ) : CubeSupport d q ≃ Support (2 ^ d) q where
  toFun S := ⟨S.val.map (positiveEquiv d).toEmbedding, by simpa using S.property⟩
  invFun S := ⟨S.val.map (positiveEquiv d).symm.toEmbedding, by simpa using S.property⟩
  left_inv S := by apply Subtype.ext; ext x; simp
  right_inv S := by apply Subtype.ext; ext x; simp
/-- Cube histories retain the original independent-pair or continuous-path carrier. -/
def CubeObs (d s : ℕ) (e : Experiment) : Type :=
  match e with
  | .pair => Fin s → Cube d × Cube d
  | .path => Fin (s + 1) → Cube d

instance cubeObsFintype (d s : ℕ) (e : Experiment) : Fintype (CubeObs d s e) := by
  cases e <;> dsimp [CubeObs] <;> infer_instance

/-- Apply the parity-preserving state bijection to every endpoint of the complete history. -/
def historyEquiv (d s : ℕ) (e : Experiment) : CubeObs d s e ≃ Obs (2 ^ d) s e :=
  match e with
  | .pair => Equiv.piCongrRight fun _ => Equiv.prodCongr (cubeEquiv d) (cubeEquiv d)
  | .path => Equiv.piCongrRight fun _ => cubeEquiv d

/-- The source profile is r on the true support, minus the compensation on its positive
complement, and zero on the negative class. -/
def cubeProfile {d q : ℕ} (r : ℝ) (S : CubeSupport d q) (x : Cube d) : ℝ := by
  classical
  exact if hx : parity x = 1 then
    if (⟨x, hx⟩ : {x : Cube d // parity x = 1}) ∈ S.val then r
    else -compensation (2 ^ d) q r
  else 0

/-- Both original directions use the actual parity kernel or its transpose. -/
def cubeKernel {d q : ℕ} (r : ℝ) (S : CubeSupport d q) (reverse : Bool)
    (x y : Cube d) : ℝ :=
  if reverse then parityKernel (cubeProfile r S) y x
  else parityKernel (cubeProfile r S) x y

/-- Uniform starts and actual edge products on the original cube. -/
def cubeProbability {d q s : ℕ} (r : ℝ) (S : CubeSupport d q)
    (reverse : Bool) (e : Experiment) (o : CubeObs d s e) : ℝ :=
  match e with
  | .pair => ∏ t : Fin s, (2 ^ (d + 1) : ℝ)⁻¹ * cubeKernel r S reverse (o t).1 (o t).2
  | .path => (2 ^ (d + 1) : ℝ)⁻¹ *
      ∏ t : Fin s, cubeKernel r S reverse (o t.castSucc) (o t.succ)

/-- Marked departures are defined directly on the original history and its parity character. -/
def cubeCount {d s : ℕ} (e : Experiment) (o : CubeObs d s e) (x : Cube d) (σ : ℝ) : ℕ :=
  match e with
  | .pair => (univ.filter fun t : Fin s => (o t).1 = x ∧ parity (o t).2 = σ).card
  | .path => (univ.filter fun t : Fin s => o t.castSucc = x ∧ parity (o t.succ) = σ).card

private theorem profile_transport {d q : ℕ} (r : ℝ) (S : CubeSupport d q) (x : Cube d) :
    cubeProfile r S x = b r (cubeSupportEquiv d q S) (cubeEquiv d x) := by
  classical
  have hp := cubeEquiv_parity d x
  cases he : cubeEquiv d x with
  | inl i =>
    have hx : parity x = 1 := by simpa [he, chi] using hp.symm
    have hi : positiveEquiv d ⟨x, hx⟩ = i := by
      have h := positiveEquiv_vertex d ⟨x, hx⟩
      rw [he] at h
      exact (Sum.inl.inj h).symm
    have hmem : i ∈ (cubeSupportEquiv d q S).val ↔
        (⟨x, hx⟩ : {x : Cube d // parity x = 1}) ∈ S.val := by
      change i ∈ S.val.map (positiveEquiv d).toEmbedding ↔ _
      rw [← hi]
      simp
    simp [cubeProfile, hx, he, b, hmem]
  | inr i =>
    have hx : parity x = -1 := by simpa [he, chi] using hp.symm
    norm_num [cubeProfile, hx, he, b]

private theorem kernel_transport {d q : ℕ} (r : ℝ) (S : CubeSupport d q)
    (reverse : Bool) (x y : Cube d) :
    cubeKernel r S reverse x y =
      if reverse then transition r (cubeSupportEquiv d q S) (cubeEquiv d y) (cubeEquiv d x)
      else transition r (cubeSupportEquiv d q S) (cubeEquiv d x) (cubeEquiv d y) := by
  have hn : (2 : ℝ) ^ (d + 1) = 2 * (2 ^ d : ℕ) := by push_cast; rw [pow_succ]; ring
  cases reverse <;> simp [cubeKernel, parityKernel, transition, profile_transport,
    ← cubeEquiv_parity, hn]

/-- Exact source/native transport preserves both kernels, complete history masses and all marked
count events. The native support is fixed before any history is sampled. -/
theorem hypercube_history_transport (d q s : ℕ) (r : ℝ) (S : CubeSupport d q)
    (reverse : Bool) (e : Experiment) :
    (∀ x : Cube d, chi (cubeEquiv d x) = parity x) ∧
    (∀ x y : Cube d, cubeKernel r S reverse x y =
      if reverse then transition r (cubeSupportEquiv d q S) (cubeEquiv d y) (cubeEquiv d x)
      else transition r (cubeSupportEquiv d q S) (cubeEquiv d x) (cubeEquiv d y)) ∧
    (∀ o : CubeObs d s e, cubeProbability r S reverse e o =
      if reverse then reverseProbability r e (cubeSupportEquiv d q S) (historyEquiv d s e o)
      else probability r e (cubeSupportEquiv d q S) (historyEquiv d s e o)) ∧
    (∀ (o : CubeObs d s e) (i : Fin (2 ^ d)) (σ : ℝ),
      cubeCount e o ((cubeEquiv d).symm (.inl i)) σ =
        count e (historyEquiv d s e o) i σ) ∧
    (∀ E : Obs (2 ^ d) s e → Prop,
      (∑ o : CubeObs d s e, if E (historyEquiv d s e o) then cubeProbability r S reverse e o else 0) =
        ∑ o : Obs (2 ^ d) s e,
          if E o then (if reverse then reverseProbability r e (cubeSupportEquiv d q S) o else probability r e (cubeSupportEquiv d q S) o) else 0) := by
  classical
  have hn : (2 : ℝ) ^ (d + 1) = 2 * (2 ^ d : ℕ) := by push_cast; rw [pow_succ]; ring
  have hm (o : CubeObs d s e) : cubeProbability r S reverse e o =
      if reverse then reverseProbability r e (cubeSupportEquiv d q S) (historyEquiv d s e o)
      else probability r e (cubeSupportEquiv d q S) (historyEquiv d s e o) := by
    cases e <;> cases reverse <;>
      simp [cubeProbability, reverseProbability, probability, historyEquiv, Equiv.piCongrRight, Pi.map_apply, kernel_transport, hn] <;> rfl
  refine ⟨cubeEquiv_parity d, kernel_transport r S reverse, hm, ?_, ?_⟩
  · intro o i σ
    have he (x : Cube d) : x = (cubeEquiv d).symm (.inl i) ↔ cubeEquiv d x = .inl i := by
      constructor
      · intro h; simp [h]
      · intro h; exact (cubeEquiv d).injective (by simpa using h)
    cases e <;>
      simp only [cubeCount, count, edges, historyEquiv, Equiv.piCongrRight,
        Equiv.prodCongr_apply, Pi.map_apply, Equiv.coe_fn_mk, ← cubeEquiv_parity, he] <;> rfl
  · intro E
    simp_rw [hm]
    convert (historyEquiv d s e).sum_comp (fun o => if E o then
      (if reverse then reverseProbability r e (cubeSupportEquiv d q S) o
       else probability r e (cubeSupportEquiv d q S) o) else (0 : ℝ)) using 1 <;> congr 1

end D5.S3.Estimation.TimeArrow.HypercubeMarkedHistory

open D5.S3.Estimation.TimeArrow.HypercubeMarkedHistory

namespace D5.S3.Estimation.TimeArrow.HypercubeMarkedPoissonAsymptotics

/-- The original logarithmic scale, indexed by cubes of dimension d+1. -/
def ell (d : ℕ) : ℝ := Real.log (2 ^ d : ℕ)

/-- The exact real observation scale; s remains an arbitrary natural number. -/
def observationScale (s : ℕ → ℕ) (d : ℕ) : ℝ := (s d : ℝ) / (2 * (2 ^ d : ℕ))

/-- Power-law support sparsity and the original observation-time limit, without a rate.
The vanishing exponent residual is exactly the meaning of q=M^(1-beta+o(1)). -/
def SourceRegime (r β α : ℝ) (q s : ℕ → ℕ) : Prop :=
  0 < r ∧ r < 1 ∧ 1 / 2 < β ∧ β < 1 ∧ 0 < α ∧
    (∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
      ∀ᶠ d in atTop, (q d : ℝ) = ((2 ^ d : ℕ) : ℝ) ^ (1 - β + δ d)) ∧
    Tendsto (fun d => observationScale s d / ell d) atTop (𝓝 α)

/-- The actual cube departure-count vector, retaining the chosen history and true support. -/
def sourceCountVector {d s k : ℕ} (e : Experiment)
    (m : Fin k → {x : Cube d // parity x = 1}) (o : CubeObs d s e) :
    (Fin k ⊕ Fin k) → ℕ :=
  Sum.elim (fun j => cubeCount e o (m j).val 1) (fun j => cubeCount e o (m j).val (-1))

/-- The mass of a count event under the original complete-history law. -/
def sourceEvent {d q s k : ℕ} (r : ℝ) (S : CubeSupport d q) (reverse : Bool)
    (m : Fin k → {x : Cube d // parity x = 1}) (e : Experiment)
    (E : Set ((Fin k ⊕ Fin k) → ℕ)) : ℝ :=
  ∑ o : CubeObs d s e, if sourceCountVector e m o ∈ E then cubeProbability r S reverse e o else 0

/-- The exact directional means: s(1 ± b)/(2n) forward and s/(2n) backward. -/
def sourceRates {d q s k : ℕ} (r : ℝ) (S : CubeSupport d q) (reverse : Bool)
    (m : Fin k → {x : Cube d // parity x = 1}) : (Fin k ⊕ Fin k) → ℝ≥0 :=
  Sum.elim
    (fun j => Real.toNNReal (((s : ℝ) / (2 * (2 ^ d : ℕ))) *
      (1 + if reverse then 0 else cubeProfile r S (m j).val) / 2))
    (fun j => Real.toNNReal (((s : ℝ) / (2 * (2 ^ d : ℕ))) *
      (1 - if reverse then 0 else cubeProfile r S (m j).val) / 2))

/-- Exact means use actual stationary adjacent-edge probabilities, for either direction. -/
def ExactDirectionalMeans {d q s k : ℕ} (r : ℝ) (S : CubeSupport d q) (reverse : Bool)
    (m : Fin k → {x : Cube d // parity x = 1}) : Prop :=
  ∀ j : Fin k,
    (∑ y : Cube d, if parity y = 1 then
      (2 ^ (d + 1) : ℝ)⁻¹ * cubeKernel r S reverse (m j).val y else 0) =
      (1 + if reverse then 0 else cubeProfile r S (m j).val) / (2 * (2 ^ (d + 1) : ℝ)) ∧
    (∑ y : Cube d, if parity y = -1 then
      (2 ^ (d + 1) : ℝ)⁻¹ * cubeKernel r S reverse (m j).val y else 0) =
      (1 - if reverse then 0 else cubeProfile r S (m j).val) / (2 * (2 ^ (d + 1) : ℝ)) ∧
    (sourceRates (s := s) r S reverse m (.inl j) : ℝ) =
      (s : ℝ) * (1 + if reverse then 0 else cubeProfile r S (m j).val) /
        (2 * (2 ^ (d + 1) : ℝ)) ∧
    (sourceRates (s := s) r S reverse m (.inr j) : ℝ) =
      (s : ℝ) * (1 - if reverse then 0 else cubeProfile r S (m j).val) /
        (2 * (2 ^ (d + 1) : ℝ))

private theorem exact_directional_means {d q s k : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < 2 ^ d) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation (2 ^ d) q r < 1) (S : CubeSupport d q)
    (reverse : Bool) (m : Fin k → {x : Cube d // parity x = 1}) :
    ExactDirectionalMeans (s := s) r S reverse m := by
  classical
  let M := 2 ^ d
  let S' := cubeSupportEquiv d q S
  have hM : (0 : ℝ) < M := by dsimp [M]; positivity
  have hn : (2 : ℝ) ^ (d + 1) = 2 * (M : ℝ) := by dsimp [M]; push_cast; rw [pow_succ]; ring
  have hbzero : (∑ i : Fin M, b r S' (.inl i)) = 0 := by
    have hh := profile_sum_zero hq hqm hr hr1 hc1 S'
    simpa [Fintype.sum_sum_type, b] using hh
  have ht := hypercube_history_transport d q s r S reverse .path
  intro j
  let i := positiveEquiv d (m j)
  have hvertex : cubeEquiv d (m j).val = .inl i := positiveEquiv_vertex d (m j)
  have hb : cubeProfile r S (m j).val = b r S' (.inl i) := by
    rw [profile_transport, hvertex]
  have htransport (σ : ℝ) :
      (∑ y : Cube d, if parity y = σ then
        (2 ^ (d + 1) : ℝ)⁻¹ * cubeKernel r S reverse (m j).val y else 0) =
      ∑ y : Vertex M, if chi y = σ then
        (2 * (M : ℝ))⁻¹ *
          (if reverse then transition r S' y (.inl i) else transition r S' (.inl i) y) else 0 := by
    simp only [kernel_transport, hvertex, ← cubeEquiv_parity, hn]
    convert (cubeEquiv d).sum_comp (fun y : Vertex M => if chi y = σ then
      (2 * (M : ℝ))⁻¹ * (if reverse then transition r S' y (.inl i)
       else transition r S' (.inl i) y) else (0 : ℝ)) using 1 <;> congr 1
  have hbp : -1 < cubeProfile r S (m j).val ∧ cubeProfile r S (m j).val < 1 := by
    rw [hb]
    have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
    dsimp [b]; split_ifs <;> constructor <;> linarith
  have hrp : 0 ≤ ((s : ℝ) / (2 * M)) *
      (1 + if reverse then 0 else cubeProfile r S (m j).val) / 2 := by
    cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · apply div_nonneg (mul_nonneg (by positivity) (by linarith [hbp.1])) (by norm_num)
    · positivity
  have hrm : 0 ≤ ((s : ℝ) / (2 * M)) *
      (1 - if reverse then 0 else cubeProfile r S (m j).val) / 2 := by
    cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · apply div_nonneg (mul_nonneg (by positivity) (by linarith [hbp.2])) (by norm_num)
    · positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [htransport, hn, hb]
    cases reverse with
    | false =>
      norm_num [Fintype.sum_sum_type, chi, transition, sum_const, M]
      field_simp
    | true =>
      simp only [↓reduceIte, Fintype.sum_sum_type, chi, transition, mul_one]
      norm_num
      rw [← mul_sum, ← sum_div, sum_add_distrib, hbzero]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, add_zero]
      field_simp <;> simp [M] <;> ring
  · rw [htransport, hn, hb]
    cases reverse <;>
      norm_num [Fintype.sum_sum_type, chi, transition, sum_const, b, M] <;>
      field_simp <;> split_ifs <;> ring
  · change (Real.toNNReal (((s : ℝ) / (2 * M)) *
      (1 + if reverse then 0 else cubeProfile r S (m j).val) / 2) : ℝ) = _
    rw [Real.coe_toNNReal _ hrp, hn]; ring
  · change (Real.toNNReal (((s : ℝ) / (2 * M)) *
      (1 - if reverse then 0 else cubeProfile r S (m j).val) / 2) : ℝ) = _
    rw [Real.coe_toNNReal _ hrm, hn]; ring

private theorem source_event_transport {d q s k : ℕ} (r : ℝ) (S : CubeSupport d q)
    (reverse : Bool) (m : Fin k → {x : Cube d // parity x = 1}) (e : Experiment)
    (E : Set ((Fin k ⊕ Fin k) → ℕ)) :
    sourceEvent (s := s) r S reverse m e E =
      ∑ o : Obs (2 ^ d) s e,
        if markedVector e (fun j => positiveEquiv d (m j)) o ∈ E then
          (if reverse then reverseProbability r e (cubeSupportEquiv d q S) o
           else probability r e (cubeSupportEquiv d q S) o) else 0 := by
  classical
  have ht := hypercube_history_transport d q s r S reverse e
  have hv (o : CubeObs d s e) : sourceCountVector e m o =
      markedVector e (fun j => positiveEquiv d (m j)) (historyEquiv d s e o) := by
    have hx (j : Fin k) : (m j).val =
        (cubeEquiv d).symm (.inl (positiveEquiv d (m j))) := by
      apply (cubeEquiv d).injective
      simpa using positiveEquiv_vertex d (m j)
    funext i
    cases i with
    | inl j =>
      change cubeCount e o (m j).val 1 = _
      rw [hx j]
      exact ht.2.2.2.1 o (positiveEquiv d (m j)) 1
    | inr j =>
      change cubeCount e o (m j).val (-1) = _
      rw [hx j]
      exact ht.2.2.2.1 o (positiveEquiv d (m j)) (-1)
  dsimp only [sourceEvent]
  simp_rw [hv]
  convert ht.2.2.2.2 (fun o => markedVector e (fun j => positiveEquiv d (m j)) o ∈ E)
    using 1 <;> congr 1

private theorem source_rates_native {d q s k : ℕ} (r : ℝ) (S : CubeSupport d q)
    (reverse : Bool) (m : Fin k → {x : Cube d // parity x = 1}) :
    sourceRates (s := s) r S reverse m =
      if reverse then (fun _ => ⟨((s : ℝ) / (2 * (2 ^ d : ℕ))) / 2, by positivity⟩ :
         (Fin k ⊕ Fin k) → ℝ≥0)
      else forwardRates (s := s) r (cubeSupportEquiv d q S) (fun j => positiveEquiv d (m j)) := by
  have hb (j : Fin k) : cubeProfile r S (m j).val =
      b r (cubeSupportEquiv d q S) (.inl (positiveEquiv d (m j))) := by
    rw [profile_transport, positiveEquiv_vertex]
  cases reverse with
  | false =>
    funext i
    cases i <;> simp [sourceRates, forwardRates, hb]
  | true =>
    funext i
    cases i <;> apply Subtype.ext <;>
      simp [sourceRates, Sum.elim_inl, Sum.elim_inr, Real.coe_toNNReal _ (by positivity :
        0 ≤ ((s : ℝ) / (2 * (2 ^ d : ℕ))) / 2)] <;> positivity

private theorem native_singleton {M s k : ℕ} (e : Experiment) (m : Fin k → Fin M)
    (o : Obs M s e) (n : (Fin k ⊕ Fin k) → ℕ) :
    markedVector e m o ∈ ({n} : Set ((Fin k ⊕ Fin k) → ℕ)) ↔
      ∀ j, count e o (m j) 1 = n (.inl j) ∧ count e o (m j) (-1) = n (.inr j) := by
  rw [Set.mem_singleton_iff]
  constructor
  · intro h j; exact ⟨congrFun h (.inl j), congrFun h (.inr j)⟩
  · intro h; funext i; cases i with
    | inl j => exact (h j).1
    | inr j => exact (h j).2

private theorem eventual_regime_controls {r β α : ℝ} {q s : ℕ → ℕ}
    (hreg : SourceRegime r β α q s) (M₀ : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ d in atTop,
      M₀ ≤ 2 ^ d ∧ 1 ≤ q d ∧ q d < 2 ^ d ∧
      compensation (2 ^ d) (q d) r ≤ 1 - (1 - r) / 2 ∧
      1 ≤ observationScale s d ∧ observationScale s d / (2 ^ d : ℕ) ≤ η ∧
      (α / 2) * ell d ≤ observationScale s d ∧
      observationScale s d ≤ (α + 1) * ell d ∧ 1 ≤ ell d := by
  obtain ⟨hr, hr1, hβ, hβ1, hα, ⟨δ, hδ, hqδ⟩, htime⟩ := hreg
  have hM (d : ℕ) : (0 : ℝ) < (2 ^ d : ℕ) := by positivity
  have hMtop : Tendsto (fun d : ℕ => ((2 ^ d : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hlogtop : Tendsto ell atTop atTop := Real.tendsto_log_atTop.comp hMtop
  have hlogsmall : Tendsto (fun d => ell d / (2 ^ d : ℕ)) atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto hMtop).tendsto_div_nhds_zero
  have hratio : Tendsto (fun d => (q d : ℝ) / (2 ^ d : ℕ)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun d => by positivity) ?_
      ((tendsto_rpow_neg_atTop (by linarith : 0 < β / 2)).comp hMtop)
    filter_upwards [hqδ, hδ.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < β / 2))]
      with d hqd hδd
    rw [hqd]
    have he : ((2 ^ d : ℕ) : ℝ) ^ (1 - β + δ d) / (2 ^ d : ℕ) =
        ((2 ^ d : ℕ) : ℝ) ^ (-β + δ d) := by
      rw [show -β + δ d = (1 - β + δ d) - 1 by ring, Real.rpow_sub (hM d), Real.rpow_one]
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le (by rw [Nat.cast_pow, Nat.cast_ofNat]; exact one_le_pow₀ (by norm_num))
      (by linarith)
  have hqpos : ∀ᶠ d in atTop, 1 ≤ q d := by
    filter_upwards [hqδ] with d hd
    have hh : (0 : ℝ) < q d := by rw [hd]; exact Real.rpow_pos_of_pos (hM d) _
    have hqN : 0 < q d := by exact_mod_cast hh
    omega
  have hqm : ∀ᶠ d in atTop, q d < 2 ^ d := by
    filter_upwards [hratio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with d hd
    have hh := (div_lt_one (hM d)).mp hd
    exact_mod_cast hh
  have hcomp : Tendsto (fun d => compensation (2 ^ d) (q d) r) atTop (𝓝 0) := by
    have hh : Tendsto (fun d => r * ((q d : ℝ) / (2 ^ d : ℕ)) /
        (1 - (q d : ℝ) / (2 ^ d : ℕ))) atTop (𝓝 0) := by
      convert (tendsto_const_nhds.mul hratio).div
        (tendsto_const_nhds.sub hratio) (by norm_num : (1 : ℝ) - 0 ≠ 0) using 1 <;>
        simp only [Pi.div_apply, Pi.mul_apply, Pi.sub_apply, mul_zero, sub_zero, zero_div]
    apply hh.congr'
    filter_upwards [hqm] with d hd
    dsimp [compensation]
    rw [Nat.cast_sub hd.le]
    field_simp [(hM d).ne']
  have hLsmall : Tendsto (fun d => observationScale s d / (2 ^ d : ℕ)) atTop (𝓝 0) := by
    have hh := htime.mul hlogsmall
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [hlogtop.eventually_gt_atTop 0] with d hd
    field_simp [hd.ne']
  filter_upwards [hMtop.eventually_ge_atTop (M₀ : ℝ), hqpos, hqm,
    hcomp.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < 1 - (1 - r) / 2)),
    hLsmall.eventually (Iio_mem_nhds hη),
    htime.eventually (Ioo_mem_nhds (by linarith : α / 2 < α) (by linarith : α < α + 1)),
    hlogtop.eventually_ge_atTop (max 1 (2 / α))] with d hMd hqd hqmd hcd hsd htd hld
  have hℓ : 1 ≤ ell d := (le_max_left _ _).trans hld
  have hℓpos : 0 < ell d := by linarith
  have hlo : (α / 2) * ell d ≤ observationScale s d := by
    exact ((lt_div_iff₀ hℓpos).mp htd.1).le
  have hhi : observationScale s d ≤ (α + 1) * ell d := by
    exact ((div_lt_iff₀ hℓpos).mp htd.2).le
  have hone : 1 ≤ observationScale s d := by
    have hh := mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hld) (show 0 ≤ α / 2 by positivity)
    have he : (α / 2) * (2 / α) = 1 := by field_simp
    rw [he] at hh
    exact hh.trans hlo
  exact ⟨by exact_mod_cast hMd, hqd, hqmd, hcd.le, hone, hsd.le, hlo, hhi, hℓ⟩

private theorem error_rescale {A α L ℓ M : ℝ} {k : ℕ}
    (hA : 0 ≤ A) (hα : 0 < α) (hL : 0 ≤ L) (hℓ : 0 ≤ ℓ) (hM : 0 < M)
    (hk : k = 1 ∨ k = 2) (hupper : L ≤ (α + 1) * ℓ) :
    A * L ^ (k + 1) / M ≤
      (2 * A * (α + 1) ^ 3) * ℓ ^ (k + 1) / (2 * M) := by
  have hp : L ^ (k + 1) ≤ ((α + 1) * ℓ) ^ (k + 1) := by gcongr
  rw [mul_pow] at hp
  have hk3 : k + 1 ≤ 3 := by rcases hk with rfl | rfl <;> omega
  have hαpow : (α + 1) ^ (k + 1) ≤ (α + 1) ^ 3 :=
    pow_le_pow_right₀ (by linarith) hk3
  have hpp := hp.trans (mul_le_mul_of_nonneg_right hαpow (pow_nonneg hℓ _))
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpp hA) hM.le
  convert hh using 1 <;> field_simp <;> ring

private theorem count_cap_rescale {α C L ℓ : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hℓ : 0 ≤ ℓ) (hlower : (α / 2) * ℓ ≤ L) :
    C * ℓ ≤ (max 1 (2 * C / α)) * L := by
  have hC₀ : 0 ≤ max 1 (2 * C / α) := le_trans (by norm_num) (le_max_left _ _)
  have hh := mul_le_mul_of_nonneg_right (le_max_right 1 (2 * C / α))
    (show 0 ≤ α / 2 by positivity)
  have he : (2 * C / α) * (α / 2) = C := by field_simp
  rw [he] at hh
  have h1 := mul_le_mul_of_nonneg_right hh hℓ
  have h2 := mul_le_mul_of_nonneg_left hlower hC₀
  nlinarith

/-- The source assumptions imply uniform relative masses on the original cube. Constants and
thresholds precede every support, marked set, direction, experiment and local count tuple. -/
theorem hypercube_marked_local_asymptotics (r α C : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hα : 0 < α) (hC : 0 < C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (β : ℝ) (q s : ℕ → ℕ),
      SourceRegime r β α q s → ∀ᶠ d in atTop,
      ∀ (k : ℕ), (k = 1 ∨ k = 2) →
        ∀ (S : CubeSupport d (q d)) (m : Fin k → {x : Cube d // parity x = 1}),
          Function.Injective m → ∀ (reverse : Bool) (e : Experiment),
            ExactDirectionalMeans (s := s d) r S reverse m ∧
            ∀ (n : (Fin k ⊕ Fin k) → ℕ),
            ((∑ i, n i : ℕ) : ℝ) ≤ C * ell d →
            let ν := poissonProduct (sourceRates (s := s d) r S reverse m)
            0 < ν.real {n} ∧
              |sourceEvent (s := s d) r S reverse m e {n} / ν.real {n} - 1| ≤
                A * (ell d) ^ (k + 1) / (2 * (2 ^ d : ℕ)) := by
  classical
  let κ := (1 - r) / 2
  let C₀ := max 1 (2 * C / α)
  have hκ : 0 < κ := by dsimp [κ]; linarith
  have hκ1 : κ < 1 := by dsimp [κ]; linarith
  have hC₀ : 1 ≤ C₀ := le_max_left _ _
  obtain ⟨Af, Mf, ηf, hAf, hMf, hηf, hf⟩ :=
    arbitrary_marked_count_poisson_relative κ C₀ hκ hκ1 hC₀
  obtain ⟨Ar, Mr, ηr, hAr, hMr, hηr, hb⟩ := actual_reverse_marked_count_relative C₀ hC₀
  let A := max Af Ar
  refine ⟨2 * A * (α + 1) ^ 3, by dsimp [A]; positivity, ?_⟩
  intro β q s hreg
  filter_upwards [eventual_regime_controls hreg (max Mf Mr) (min ηf ηr) (lt_min hηf hηr)]
    with d hd
  obtain ⟨hMd, hqd, hqmd, hcd, hLd, hsd, hlo, hhi, hℓ⟩ := hd
  intro k hk S m hm reverse e
  have hc1d : compensation (2 ^ d) (q d) r < 1 := by linarith
  refine ⟨exact_directional_means hqd hqmd hr hr1 hc1d S reverse m, ?_⟩
  intro n hn ν
  let M := 2 ^ d
  let L := observationScale s d
  let S' := cubeSupportEquiv d (q d) S
  let m' := fun j => positiveEquiv d (m j)
  haveI : IsProbabilityMeasure ν := by dsimp [ν, poissonProduct]; infer_instance
  have hm' : Function.Injective m' := (positiveEquiv d).injective.comp hm
  have hM : (0 : ℝ) < M := by dsimp [M]; positivity
  have hc1 : compensation M (q d) r < 1 := by dsimp [M, κ] at *; linarith
  have hcap := count_cap_rescale hα hC.le (by linarith : 0 ≤ ell d) hlo
  have hcounts (j : Fin k) : (n (.inl j) : ℝ) ≤ C₀ * L ∧ (n (.inr j) : ℝ) ≤ C₀ * L := by
    have hp : n (.inl j) ≤ ∑ i, n i := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ _)
    have hm : n (.inr j) ≤ ∑ i, n i := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ _)
    constructor
    · exact (show (n (.inl j) : ℝ) ≤ (∑ i, n i : ℕ) by exact_mod_cast hp).trans (hn.trans hcap)
    · exact (show (n (.inr j) : ℝ) ≤ (∑ i, n i : ℕ) by exact_mod_cast hm).trans (hn.trans hcap)
  have hP := source_event_transport (s := s d) r S reverse m e ({n} : Set ((Fin k ⊕ Fin k) → ℕ))
  simp_rw [native_singleton] at hP
  have hν := source_rates_native (s := s d) r S reverse m
  have hAfA : Af ≤ A := le_max_left _ _
  have hArA : Ar ≤ A := le_max_right _ _
  have hA : 0 ≤ A := hAf.le.trans hAfA
  have herr := error_rescale hA hα (by linarith : 0 ≤ L)
    (by linarith : 0 ≤ ell d) hM hk hhi
  cases reverse with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hν hP
    have hvals := forward_rate_values (s := s d) (by positivity) hqd hqmd hr hr1 hc1 S' m'
    dsimp only [S', m'] at hvals
    have hQ : ν.real {n} = ∏ j : Fin k,
        (Real.exp (-(L * (1 + b r S' (.inl (m' j))) / 2)) *
          (L * (1 + b r S' (.inl (m' j))) / 2) ^ n (.inl j) / (n (.inl j)).factorial) *
        (Real.exp (-(L * (1 - b r S' (.inl (m' j))) / 2)) *
          (L * (1 - b r S' (.inl (m' j))) / 2) ^ n (.inr j) / (n (.inr j)).factorial) := by
      dsimp only [ν]
      rw [hν, poisson_product_singleton, Fintype.prod_sum_type]
      simp_rw [hvals.1, hvals.2.1]
      rw [← prod_mul_distrib]
      rfl
    have hcNonneg : 0 ≤ compensation (2 ^ d) (q d) r := by unfold compensation; positivity
    have hbnd (j : Fin k) : -(1 - κ) ≤ b r S' (.inl (m' j)) ∧
        b r S' (.inl (m' j)) ≤ 1 - κ := by
      dsimp [b]; split_ifs <;> dsimp [κ] at * <;> constructor <;> linarith
    have hμp (j : Fin k) : 0 < L * (1 + b r S' (.inl (m' j))) / 2 := by
      have hh := (hbnd j).1; have hLp : 0 < L := by linarith
      apply div_pos (mul_pos hLp (by linarith)) (by norm_num)
    have hμm (j : Fin k) : 0 < L * (1 - b r S' (.inl (m' j))) / 2 := by
      have hh := (hbnd j).2; have hLp : 0 < L := by linarith
      apply div_pos (mul_pos hLp (by linarith)) (by norm_num)
    have hνpos : 0 < ν.real {n} := by
      rw [hQ]
      exact prod_pos fun j _ => mul_pos
        (div_pos (mul_pos (Real.exp_pos _) (pow_pos (hμp j) _)) (by positivity))
        (div_pos (mul_pos (Real.exp_pos _) (pow_pos (hμm j) _)) (by positivity))
    refine ⟨hνpos, ?_⟩
    have hh := hf M (q d) (s d) k r ((le_max_left _ _).trans hMd) hqd hqmd hr
      (by dsimp [κ]; linarith) hcd hLd (hsd.trans (min_le_left _ _)) hk
      S' m' hm' (fun j => n (.inl j)) (fun j => n (.inr j)) hcounts e
    rw [hP, hQ]
    exact hh.trans ((div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAfA (by positivity : 0 ≤ L ^ (k + 1))) hM.le).trans herr)
  | true =>
    simp only [↓reduceIte] at hν hP
    let μ : (Fin k ⊕ Fin k) → ℝ≥0 := fun _ => ⟨L / 2, by positivity⟩
    have hν' : sourceRates (s := s d) r S true m = μ := hν
    have hQ : ν.real {n} = ∏ j : Fin k,
        (Real.exp (-(L / 2)) * (L / 2) ^ n (.inl j) / (n (.inl j)).factorial) *
        (Real.exp (-(L / 2)) * (L / 2) ^ n (.inr j) / (n (.inr j)).factorial) := by
      dsimp only [ν]
      rw [hν', poisson_product_singleton, Fintype.prod_sum_type, ← prod_mul_distrib]
      rfl
    refine ⟨by rw [hQ]; exact prod_pos fun j _ => by positivity, ?_⟩
    have hh := hb M (q d) (s d) k r ((le_max_right _ _).trans hMd) hqd hqmd hr hr1
      hc1 hLd (hsd.trans (min_le_right _ _)) hk S' m' hm'
      (fun j => n (.inl j)) (fun j => n (.inr j)) hcounts e
    rw [hP, hQ]
    exact hh.trans ((div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hArA (by positivity : 0 ≤ L ^ (k + 1))) hM.le).trans herr)

private theorem exponential_tail_rescale {α D L ℓ M : ℝ} {k : ℕ}
    (hα : 0 < α) (hD : 0 < D) (hM : 0 < M) (hℓ : ℓ = Real.log M)
    (hℓlarge : Real.log 6 ≤ ℓ) (hk : k = 1 ∨ k = 2)
    (hL : 0 ≤ L) (hupper : L ≤ (α + 1) * ℓ) :
    let C := (2 * (α + 1) + D + 2) / Real.log 2
    3 * Real.exp ((k : ℝ) * L) / (2 : ℝ) ^ ⌊C * ℓ⌋₊ ≤ M ^ (-D) := by
  intro C
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hℓpos : 0 < ℓ := (Real.log_pos (by norm_num : (1 : ℝ) < 6)).trans_le hℓlarge
  have hC : 0 < C := by dsimp [C]; positivity
  have hfloor := Nat.lt_floor_add_one (C * ℓ)
  have hprod : C * Real.log 2 = 2 * (α + 1) + D + 2 := by dsimp [C]; field_simp
  have hk2 : (k : ℝ) ≤ 2 := by rcases hk with rfl | rfl <;> norm_num
  have hkl : (k : ℝ) * L ≤ 2 * ((α + 1) * ℓ) := by nlinarith
  have hbf := mul_lt_mul_of_pos_right hfloor hlog2
  have hlog6 : Real.log 3 + Real.log 2 = Real.log 6 := by
    rw [← Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hexponent : Real.log 3 + (k : ℝ) * L -
      (⌊C * ℓ⌋₊ : ℝ) * Real.log 2 ≤ -D * ℓ := by
    have he : (C * ℓ) * Real.log 2 = (2 * (α + 1) + D + 2) * ℓ := by
      rw [mul_right_comm, hprod]
    nlinarith
  have hden : (2 : ℝ) ^ ⌊C * ℓ⌋₊ = Real.exp ((⌊C * ℓ⌋₊ : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  calc
    _ = Real.exp (Real.log 3 + (k : ℝ) * L - (⌊C * ℓ⌋₊ : ℝ) * Real.log 2) := by
      rw [Real.exp_sub, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3),
        ← hden]
    _ ≤ Real.exp (-D * ℓ) := Real.exp_le_exp.mpr hexponent
    _ = M ^ (-D) := by rw [Real.rpow_def_of_pos hM, hℓ]; congr 1; ring

/-- Every-D tails and every-event relative-plus-additive comparison hold on the original cube.
The cutoff and relative constant are fixed before d and all actual statistical objects. -/
theorem hypercube_marked_tail_event_asymptotics (r α D : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hα : 0 < α) (hD : 0 < D) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ (β : ℝ) (q s : ℕ → ℕ),
      SourceRegime r β α q s → ∀ᶠ d in atTop,
      ∀ (k : ℕ), (k = 1 ∨ k = 2) →
        ∀ (S : CubeSupport d (q d)) (m : Fin k → {x : Cube d // parity x = 1}),
          Function.Injective m → ∀ (reverse : Bool) (e : Experiment),
            let ν := poissonProduct (sourceRates (s := s d) r S reverse m)
            sourceEvent (s := s d) r S reverse m e {n | C * ell d < ((∑ i, n i : ℕ) : ℝ)} +
                ν.real {n | C * ell d < ((∑ i, n i : ℕ) : ℝ)} ≤
              ((2 ^ d : ℕ) : ℝ) ^ (-D) ∧
            ∀ E : Set ((Fin k ⊕ Fin k) → ℕ),
              |sourceEvent (s := s d) r S reverse m e E - ν.real E| ≤
                (A * (ell d) ^ (k + 1) / (2 * (2 ^ d : ℕ))) * ν.real E +
                  ((2 ^ d : ℕ) : ℝ) ^ (-D) := by
  classical
  let κ := (1 - r) / 2
  let C := (2 * (α + 1) + D + 2) / Real.log 2
  let C₀ := max 1 (2 * C / α)
  have hκ : 0 < κ := by dsimp [κ]; linarith
  have hκ1 : κ < 1 := by dsimp [κ]; linarith
  have hC : 0 < C := by dsimp [C]; exact div_pos (by linarith) (Real.log_pos (by norm_num))
  have hC₀ : 1 ≤ C₀ := le_max_left _ _
  obtain ⟨Af, Mf, ηf, hAf, hMf, hηf, hf⟩ := actual_forward_marked_every_event κ C₀ hκ hκ1 hC₀
  obtain ⟨Ar, Mr, ηr, hAr, hMr, hηr, hb⟩ := actual_reverse_marked_every_event C₀ hC₀
  let A := max Af Ar
  refine ⟨C, 2 * A * (α + 1) ^ 3, hC, by dsimp [A]; positivity, ?_⟩
  intro β q s hreg
  have hMtop : Tendsto (fun d : ℕ => ((2 ^ d : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  filter_upwards [eventual_regime_controls hreg (max Mf Mr)
    (min (min ηf ηr) (1 / 512)) (lt_min (lt_min hηf hηr) (by norm_num)),
    (Real.tendsto_log_atTop.comp hMtop).eventually_ge_atTop (Real.log 6)] with d hd hdlog
  obtain ⟨hMd, hqd, hqmd, hcd, hLd, hsd, hlo, hhi, hℓ⟩ := hd
  intro k hk S m hm reverse e ν
  let M := 2 ^ d
  let L := observationScale s d
  let B := ⌊C * ell d⌋₊
  let S' := cubeSupportEquiv d (q d) S
  let m' := fun j => positiveEquiv d (m j)
  haveI : IsProbabilityMeasure ν := by dsimp [ν, poissonProduct]; infer_instance
  have hm' : Function.Injective m' := (positiveEquiv d).injective.comp hm
  have hM64 : 64 ≤ M := hMf.trans ((le_max_left _ _).trans hMd)
  have hM : (0 : ℝ) < M := by dsimp [M]; positivity
  have hc1 : compensation M (q d) r < 1 := by dsimp [M, κ] at *; linarith
  have hsmall : (s d : ℝ) / (M : ℝ) ^ 2 ≤ 1 / 256 := by
    have hs := hsd.trans (min_le_right _ _)
    have he : (s d : ℝ) / (M : ℝ) ^ 2 = 2 * (L / M) := by
      dsimp [L, observationScale, M]; field_simp
    rw [he]; linarith
  have hB : (B : ℝ) ≤ C₀ * L :=
    (Nat.floor_le (by positivity : 0 ≤ C * ell d)).trans
      (count_cap_rescale hα hC.le (by linarith : 0 ≤ ell d) hlo)
  have htailnum : 3 * Real.exp ((k : ℝ) * L) / (2 : ℝ) ^ B ≤ (M : ℝ) ^ (-D) :=
    exponential_tail_rescale hα hD hM rfl hdlog hk (by linarith) hhi
  have hAfA : Af ≤ A := le_max_left _ _
  have hArA : Ar ≤ A := le_max_right _ _
  have hA : 0 ≤ A := hAf.le.trans hAfA
  have herr := error_rescale hA hα (by linarith : 0 ≤ L)
    (by linarith : 0 ≤ ell d) hM hk hhi
  have hν := source_rates_native (s := s d) r S reverse m
  have hc : 0 ≤ compensation M (q d) r := by unfold compensation; positivity
  have hK := ((finite_support_bayes (s := s d) hqd hqmd hr hr1 hc hc1 e).1 S').1.1
  have hw (o : Obs M (s d) e) :
      0 ≤ (if reverse then reverseProbability r e S' o else probability r e S' o) := by
    cases reverse with
    | false =>
      change 0 ≤ probability r e S' o
      cases e with
      | pair => exact prod_nonneg fun t _ => mul_nonneg (by positivity) (hK _ _)
      | path => exact mul_nonneg (by positivity) (prod_nonneg fun t _ => hK _ _)
    | true =>
      change 0 ≤ reverseProbability r e S' o
      cases e with
      | pair => exact prod_nonneg fun t _ => mul_nonneg (by positivity) (hK _ _)
      | path => exact mul_nonneg (by positivity) (prod_nonneg fun t _ => hK _ _)
  have hsubset : {n : (Fin k ⊕ Fin k) → ℕ | C * ell d < ((∑ i, n i : ℕ) : ℝ)} ⊆
      {n | B < ∑ i, n i} := by
    intro n hn
    have hh : (B : ℝ) < ((∑ i, n i : ℕ) : ℝ) := (Nat.floor_le (by positivity : 0 ≤ C * ell d)).trans_lt hn
    exact_mod_cast hh
  have hsource_mono : sourceEvent (s := s d) r S reverse m e
      {n | C * ell d < ((∑ i, n i : ℕ) : ℝ)} ≤
      sourceEvent (s := s d) r S reverse m e {n | B < ∑ i, n i} := by
    rw [source_event_transport, source_event_transport]
    apply sum_le_sum
    intro o _
    change (@ite ℝ (markedVector e m' o ∈ {n | C * ell d < ((∑ i, n i : ℕ) : ℝ)})
      (Classical.propDecidable _) (if reverse then reverseProbability r e S' o else probability r e S' o) 0) ≤
      @ite ℝ (markedVector e m' o ∈ {n | B < ∑ i, n i}) (Classical.propDecidable _)
        (if reverse then reverseProbability r e S' o else probability r e S' o) 0
    by_cases h : markedVector e m' o ∈ {n | C * ell d < ((∑ i, n i : ℕ) : ℝ)}
    · simp only [if_pos h, if_pos (hsubset h)]; exact le_rfl
    · simp only [if_neg h]
      by_cases hb : markedVector e m' o ∈ {n | B < ∑ i, n i}
      · rw [if_pos hb]; exact hw o
      · rw [if_neg hb]
  have hpoisson_mono : ν.real {n | C * ell d < ((∑ i, n i : ℕ) : ℝ)} ≤
      ν.real {n | B < ∑ i, n i} := measureReal_mono hsubset
  have hcounts (o : Obs M (s d) e) : (∑ i, markedVector e m' o i) =
      ∑ j, (count e o (m' j) 1 + count e o (m' j) (-1)) := by
    simp [markedVector, Fintype.sum_sum_type, sum_add_distrib]
  constructor
  · apply (add_le_add hsource_mono hpoisson_mono).trans
    rw [source_event_transport]
    simp only [Set.mem_setOf_eq]
    change (∑ o : Obs M (s d) e, if B < ∑ i, markedVector e m' o i then
      (if reverse then reverseProbability r e S' o else probability r e S' o) else 0) +
      ν.real {n | B < ∑ i, n i} ≤ _
    simp_rw [hcounts]
    cases reverse with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hν
      dsimp only [ν]
      rw [hν]
      exact (actual_forward_marked_count_tail hM64 hqd hqmd hr hr1 hc1 hk S' m' hm' e hsmall B).trans htailnum
    | true =>
      simp only [↓reduceIte] at hν
      dsimp only [ν]
      rw [hν]
      exact (actual_reverse_marked_count_tail hM64 hqd hqmd hr hr1 hc1 hk S' m' hm' e hsmall B).trans htailnum
  · intro E
    have hνnonneg : 0 ≤ ν.real E := measureReal_nonneg
    rw [source_event_transport]
    cases reverse with
    | false =>
      have hh := hf M (q d) (s d) k r ((le_max_left _ _).trans hMd) hqd hqmd hr
        (by dsimp [κ]; linarith) hcd hLd
        (hsd.trans ((min_le_left _ _).trans (min_le_left _ _))) hk S' m' hm' e B hB E
      simp only [Bool.false_eq_true, ↓reduceIte] at hν
      dsimp only [ν]
      rw [hν]
      apply hh.trans
      apply add_le_add _ htailnum
      apply mul_le_mul_of_nonneg_right _ (measureReal_nonneg (μ := poissonProduct _) (s := E))
      exact (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hAfA (by positivity : 0 ≤ L ^ (k + 1))) hM.le).trans herr
    | true =>
      have hh := hb M (q d) (s d) k r ((le_max_right _ _).trans hMd) hqd hqmd hr hr1
        hc1 hLd (hsd.trans ((min_le_left _ _).trans (min_le_right _ _))) hk S' m' hm' e B hB E
      simp only [Bool.false_eq_true, ↓reduceIte] at hν
      dsimp only [ν]
      rw [hν]
      apply hh.trans
      apply add_le_add _ htailnum
      apply mul_le_mul_of_nonneg_right _ (measureReal_nonneg (μ := poissonProduct _) (s := E))
      exact (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hArA (by positivity : 0 ≤ L ^ (k + 1))) hM.le).trans herr

end D5.S3.Estimation.TimeArrow.HypercubeMarkedPoissonAsymptotics
