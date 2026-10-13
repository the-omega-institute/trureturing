/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteStochasticMixing
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteStochasticMixing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite primitive stochastic matrices converge to their unique stationary probability row. -/

/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.UniformSpace.Matrix
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Lp.PiLp

import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRowLimits

open Finset NNReal WithLp Matrix PiLp Nat ContractingWith Metric Bornology Filter Function
open scoped BigOperators
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteStochasticMixing

universe u
variable {S : Type u} [Fintype S]
abbrev l1Space (S : Type u) := WithLp 1 (S → ℝ)
local instance : Coe (S → ℝ) (l1Space S) := ⟨WithLp.toLp 1⟩

local notation "‖"x"‖₁" => (nnnorm (E := l1Space S) (WithLp.toLp 1 (x : S → ℝ)))
local notation "d₁("x","y")" => edist (α := l1Space S) x y

class StochasticVec (x : S → ℝ) where
  nonneg : ∀ s, 0 ≤ x s
  rowsum : ∑ s, x s = 1

section simplex

abbrev Simplex (S : Type u) [Fintype S] := {x : l1Space S | StochasticVec x}

instance (x : ↑(Simplex S)) : @StochasticVec S _ x := by exact x.property

instance : IsClosed (Simplex S) := by
  let l1Space := l1Space S
  have h1 : IsClosed {f : l1Space | ∀ s, 0 ≤ f s} := by
    have hcl (s : S) : IsClosed {f : l1Space | 0 ≤ f s} := by
      have hev : Continuous (fun f : l1Space => f s) := by
        exact PiLp.continuous_apply 1 (fun _ : S => ℝ) s
      have half : IsClosed {x : ℝ | 0 ≤ x} :=
        isClosed_le continuous_const continuous_id
      simpa [Set.preimage] using half.preimage hev
    simpa [Set.setOf_forall] using isClosed_iInter hcl
  have h2 : IsClosed {f : l1Space | (∑ s, f s) = 1} := by
    have hsum : Continuous (fun f : l1Space => ∑ s, f s) := by
      simpa using continuous_finset_sum (s := (Finset.univ : Finset S))
        (fun s _ => PiLp.continuous_apply 1 (fun _ : S => ℝ) s)
    have htarget : IsClosed ({x : ℝ | x = 1} : Set ℝ) := by simp
    simpa [Set.preimage] using htarget.preimage hsum
  have h := IsClosed.inter h1 h2
  simp [←Set.setOf_and] at h
  have : {x : l1Space | StochasticVec x} =
    {x | (∀ s, 0 ≤ x s) ∧ (∑ s, x s = 1)} := by
    ext1; simp; constructor
    · intro h; exact ⟨h.nonneg, h.rowsum⟩
    · intro h; exact ⟨h.1, h.2⟩
  unfold Simplex
  rw [this]
  exact h

instance : CompleteSpace (Simplex S) := by
  apply IsClosed.completeSpace_coe

private lemma l1_norm_eq_sum (f : l1Space S) : ‖f‖ = ∑ s, |f s| := by
  simpa using (PiLp.norm_eq_sum (f := f))

private lemma l1_norm_eq_one (x : S → ℝ) [StochasticVec x]
  : ‖x‖₁ = 1 := by
  apply NNReal.eq
  simp [l1_norm_eq_sum]
  have hx := (inferInstance : StochasticVec x)
  rw [←hx.rowsum]
  apply sum_congr rfl
  intro s hs
  rw [abs_of_nonneg (hx.nonneg s)]

end simplex

class RowStochastic (P : Matrix S S ℝ) where
  stochastic: ∀ s, StochasticVec (P s)

private theorem row_stochastic_mem [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] : P ∈ Matrix.rowStochastic ℝ S :=
  Matrix.mem_rowStochastic_iff_sum.mpr ⟨fun i =>
    ((inferInstance : RowStochastic P).stochastic i).nonneg,
    fun i => ((inferInstance : RowStochastic P).stochastic i).rowsum⟩

instance svec_mul_smat_is_svec
  (μ : S → ℝ) [StochasticVec μ] (P : Matrix S S ℝ) [RowStochastic P] :
  StochasticVec (μ ᵥ* P) := by
  classical
  have hP := row_stochastic_mem P
  have hμ := (inferInstance : StochasticVec μ)
  refine ⟨Matrix.nonneg_vecMul_of_mem_rowStochastic hP hμ.nonneg, ?_⟩
  simpa [dotProduct] using Matrix.vecMul_dotProduct_one_eq_one_rowStochastic hP
    (x := μ) (by simpa [dotProduct] using hμ.rowsum)

instance smat_pow_is_smat [DecidableEq S]
  (P : Matrix S S ℝ) [RowStochastic P] (n : ℕ) :
  RowStochastic (P ^ n) := by
  have h := (Matrix.rowStochastic ℝ S).pow_mem (row_stochastic_mem P) n
  exact ⟨fun i => ⟨fun _ => Matrix.nonneg_of_mem_rowStochastic h,
    Matrix.sum_row_of_mem_rowStochastic h i⟩⟩

private lemma chapman_kolmogorov_eq_ge [DecidableEq S]
  (P : Matrix S S ℝ) [RowStochastic P] (m n : ℕ) (i j : S) :
  ∀ k, (P ^ (m + n)) i j ≥ (P ^ m) i k * (P ^ n) k j := by
  have hP := (inferInstance : RowStochastic P).stochastic
  intro k
  rw [pow_add]
  simp [Matrix.mul_apply]
  rw [←sum_erase_add (a := k)]
  apply sub_nonneg.mp
  rw [add_sub_cancel_right]
  apply sum_nonneg
  intro l hl
  apply mul_nonneg
  · have hP := RowStochastic.stochastic (P := P ^ m)
    exact (hP i).nonneg l
  · have hP := RowStochastic.stochastic (P := P ^ n)
    exact (hP l).nonneg j
  · simp

class ClosedUnderAdd (A : Set ℕ) : Prop where
  closed_under_add : ∀ ⦃a b⦄, a ∈ A → b ∈ A → a + b ∈ A

class FiniteGCDOne (A : Set ℕ) : Prop where
  finite_gcd_one : ∃ s : Finset ℕ,
    (s : Set ℕ) ⊆ A ∧ s.gcd id = 1 ∧ 0 ∉ s ∧ s.Nonempty

private theorem all_but_finite_of_closed_under_add_and_gcd_one
    {A : Set ℕ} [ClosedUnderAdd A] [FiniteGCDOne A] :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → n ∈ A := by
  obtain ⟨s, hsA, hsG, _, _⟩ := (inferInstance : FiniteGCDOne A).finite_gcd_one
  have hG : Nat.setGcd A = 1 := by
    apply Nat.dvd_one.mp
    rw [← hsG]
    exact Finset.dvd_gcd_iff.mpr fun n hn => Nat.setGcd_dvd_of_mem (hsA hn)
  obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge A
  refine ⟨N + 1, fun n hn => ?_⟩
  have hm := hN n (by omega) (hG ▸ one_dvd n)
  have hclosure : ∀ m ∈ AddSubmonoid.closure A, m = 0 ∨ m ∈ A := by
    intro m hm
    induction hm using AddSubmonoid.closure_induction with
    | mem x hx => exact Or.inr hx
    | zero => exact Or.inl rfl
    | add x y _ _ hx hy =>
      rcases hx with rfl | hx
      · simpa using hy
      rcases hy with rfl | hy
      · simpa using (Or.inr hx : x = 0 ∨ x ∈ A)
      exact Or.inr (ClosedUnderAdd.closed_under_add hx hy)
  exact (hclosure n hm).resolve_left (by omega)

section minorization

variable [DecidableEq S]

class Irreducible (P : Matrix S S ℝ) [RowStochastic P] where
  irreducible : ∀ i j, ∃ n : ℕ, 0 < (P ^ n) i j

noncomputable def return_times (P : Matrix S S ℝ) [RowStochastic P] (i : S)
  : Set ℕ :=  {n : ℕ | 1 ≤ n ∧ 0 < (P ^ n) i i}

instance (P : Matrix S S ℝ) [RowStochastic P] (i : S)
  : ClosedUnderAdd (return_times P i) := by
  constructor
  intro a b ha hb
  simp only [return_times, Set.mem_setOf_eq] at ha hb ⊢
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  constructor
  · linarith
  · calc
      0 < (P ^ a) i i * (P ^ b) i i := by
        exact mul_pos ha2 hb2
    _ ≤ (P ^ (a + b)) i i := by
      exact (chapman_kolmogorov_eq_ge P a b i i i).le

class Aperiodic (P : Matrix S S ℝ) [RowStochastic P] where
  aperiodic : ∀ i, FiniteGCDOne (return_times P i)

instance (P : Matrix S S ℝ) [RowStochastic P] [Aperiodic P] (i : S)
  : FiniteGCDOne (return_times P i) := by
  exact (inferInstance : Aperiodic P).aperiodic i

private theorem eventually_positive [Nonempty S] (P : Matrix S S ℝ) [RowStochastic P]
  [Irreducible P] [Aperiodic P] :
  ∃ N, ∀ n i j, N ≤ n → 0 < (P ^ n) i j := by
  let h_exists_ni := fun i =>
    (all_but_finite_of_closed_under_add_and_gcd_one
      (A := (return_times P i)))
  let ni := fun i => (h_exists_ni i).choose
  have : ∃ N, ∀ n i, N ≤ n → 0 < (P ^ n) i i := by
    have : (Finset.univ (α := S)).Nonempty := by simp
    refine ⟨?N, ?hN⟩
    case N => exact sup' (Finset.univ (α := S)) this ni
    case hN =>
      intro n i hnge
      have hni : ni i ≤ n := by
        have : i ∈ Finset.univ (α := S) := by simp
        have := le_sup' ni this
        linarith
      have := (h_exists_ni i).choose_spec n hni
      simp [return_times] at this
      exact this.2
  obtain ⟨n₀, hn₀⟩ := this
  let h_exists_nij := fun ij : S × S =>
    (inferInstance : Irreducible P).irreducible ij.1 ij.2
  let nij := fun ij => (h_exists_nij ij).choose
  have : (Finset.univ (α := S × S)).Nonempty := by simp
  let n₁ := sup' (Finset.univ (α := S × S)) this nij
  refine ⟨?N, ?hN⟩
  case N => exact n₀ + n₁
  case hN =>
    intro n i j hnge
    let ij := nij (i, j)
    have : ij ≤ n₁ := by
      have : (i, j) ∈ Finset.univ (α := S × S) := by simp
      exact le_sup' nij this
    have hnijn : ij ≤ n := by linarith
    have hn : n₀ ≤ n - ij := by
      rw [Nat.le_sub_iff_add_le hnijn]
      linarith
    have hPnij : 0 < (P ^ (ij)) i j := by
      simp [ij]; exact (h_exists_nij (i, j)).choose_spec
    have hPn₀ : 0 < (P ^ (n - ij)) j j := hn₀ (n - ij) j hn
    calc
      0
    _ < (P ^ (ij)) i j * (P ^ (n - ij)) j j := by
      exact mul_pos hPnij hPn₀
    _ ≤ (P ^ n) i j := by
      have hineq := chapman_kolmogorov_eq_ge P (ij) (n - ij) i j j
      have : ij + (n - ij) = n := by
        rw [add_comm, Nat.sub_add_cancel hnijn]
      rw [this] at hineq
      exact hineq.le

class DoeblinMinorization (P : Matrix S S ℝ) [RowStochastic P] where
  minorize : ∃ (ε : ℝ) (ν : S → ℝ),
    0 < ε ∧ ε < 1 ∧ StochasticVec ν ∧ ∀ i j, P i j ≥ ε * ν j

private theorem smat_minorizable_with_large_pow
  [Nonempty S] (P : Matrix S S ℝ)
  [RowStochastic P] [Irreducible P] [Aperiodic P] :
  ∃ N, 1 ≤ N ∧ DoeblinMinorization (P ^ N) := by
  obtain ⟨n₀, hn₀⟩ := eventually_positive P
  let n₁ := n₀ + 1
  have hn₀ := hn₀ n₁
  let hnij := fun ij : S × S => hn₀ ij.1 ij.2 (by unfold n₁; simp)
  have : (Finset.univ (α := S × S)).Nonempty := by simp
  let δij := fun ij : S × S => (P ^ n₁) ij.1 ij.2
  let δ := inf' (Finset.univ (α := S × S)) this δij
  have hδinf : ∀ ij, δ ≤ δij ij := by
    intro ij
    have : ij ∈ Finset.univ (α := S × S) := by simp
    have := inf'_le (f := δij) this
    exact this
  have hδrange : 0 < δ ∧ δ ≤ 1:= by
    obtain ⟨ij, hij, hijinf⟩ := exists_mem_eq_inf' this δij
    have hδdef : δ = δij ij := by unfold δ; simp [hijinf]
    unfold δij at this
    have := hnij ij
    constructor
    case left => linarith
    case right =>
      obtain ⟨nonneg, rowsum⟩ := RowStochastic.stochastic (P := P ^ n₁) (ij.1)
      rw [hδdef, ←rowsum, ←sum_erase_add (a := ij.2) (h := by simp)]
      unfold δij
      apply sub_nonneg.mp
      rw [add_sub_cancel_right]
      apply sum_nonneg
      · intro j hj; exact nonneg j
  let δ' := δ * 1 / 2 * 1 / Fintype.card S
  refine ⟨n₁, ?hNpos, ?hN⟩
  case hNpos => unfold n₁; simp
  case hN =>
    constructor
    let ν : S → ℝ := fun j => 1 / Fintype.card S
    refine ⟨?ε, ?ν, ?hεpos, ?hεlt1, ?hν, ?hP⟩
    case ε => exact δ' * Fintype.card S
    case hεlt1 => unfold δ'; simp; linarith
    case hεpos => unfold δ'; simp; linarith
    case ν => exact ν
    case hν =>
      constructor
      case nonneg => intro s; simp [ν]
      case rowsum =>
      simp [ν, Finset.sum_const, Finset.card_univ]
    case hP =>
      intro i j
      have := hδinf (i, j)
      simp [δij] at this
      simp [ν]
      unfold δ'
      have : δ * 1 / 2 * 1 / Fintype.card S ≤ δ := by
        simp
        rw [div_div]
        apply mul_le_of_le_one_right (ha := hδrange.1.le) _
        have : 0 < Fintype.card S := by
          apply Fintype.card_pos_iff.mpr inferInstance
        have : 1 ≤ 2 * Fintype.card S := by linarith [Nat.le_of_lt this]
        set z := (2 : ℝ) * Fintype.card S
        have h1lez : 1 ≤ z := by unfold z; exact_mod_cast this
        have hpos : 0 < z := by linarith
        apply (inv_le_comm₀ hpos (by simp)).mpr
        simp
        exact h1lez
      linarith

end minorization

section contraction

private def broadcast (ν : S → ℝ) : Matrix S S ℝ :=
  Matrix.of (fun _ s' => ν s')

private lemma vecMul_broadcast (v : S → ℝ) (ν : S → ℝ) [StochasticVec ν] :
    v ᵥ* broadcast ν = fun j => (∑ i, v i) * ν j := by
  classical
  funext j
  simp [broadcast, Matrix.vecMul, Finset.sum_mul, dotProduct]

private theorem smat_nonexpansive_in_l1 (Q : Matrix S S ℝ) [RowStochastic Q] :
    ∀ (x y : S → ℝ),
      ‖x ᵥ* Q - y ᵥ* Q‖₁ ≤ ‖x - y‖₁ := by
  intro x y
  have hQ := (inferInstance : RowStochastic Q).stochastic
  have hxy : x ᵥ* Q - y ᵥ* Q = fun j => ∑ i, (x i - y i) * Q i j := by
    funext j
    simp [Matrix.vecMul, sub_eq_add_neg, sub_eq_add_neg, sum_add_distrib, add_mul, dotProduct]
  have hnorm : ‖x ᵥ* Q - y ᵥ* Q‖₁ = ∑ j, |∑ i, (x i - y i) * Q i j| := by
    have := l1_norm_eq_sum (WithLp.toLp 1 (x ᵥ* Q - y ᵥ* Q))
    conv_rhs at this => rw [hxy]
    exact this
  have : ∑ j, |∑ i, (x i - y i) * Q i j| ≤ ‖x - y‖₁ := by
    calc
      ∑ j, |∑ i, (x i - y i) * Q i j|
    _ ≤ ∑ j, ∑ i, |(x i - y i) * Q i j| := by
      apply sum_le_sum
      · intro j _; exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ i, |(x i - y i)| * Q i j := by
      apply sum_le_sum
      · intro j _; apply sum_le_sum;
        · intro i _; simp [abs_mul]; simp [abs_of_nonneg ((hQ i).nonneg j)]
    _ = ∑ i, |x i - y i| * (∑ j, Q i j) := by
      conv_lhs => rw [Finset.sum_comm]
      simp [mul_comm, sum_mul]
    _ = ∑ i, |x i - y i| := by
      apply sum_congr rfl
      · intro i _; simp [(hQ i).rowsum]
    _ = ‖x - y‖₁ := by simp [l1_norm_eq_sum]
  refine (NNReal.coe_le_coe.mp ?_)
  linarith

def smat_as_operator (P : Matrix S S ℝ) [RowStochastic P] :
  ↑(Simplex S) → ↑(Simplex S) :=
  fun μ => ⟨μ.val ᵥ* P, by
    exact svec_mul_smat_is_svec μ P
  ⟩

private lemma smat_as_operator_iter [DecidableEq S]
  (P : Matrix S S ℝ) [RowStochastic P] (n : ℕ)
  : (smat_as_operator P)^[n] = fun μ => ⟨μ.val ᵥ* (P ^ n), by
    exact svec_mul_smat_is_svec μ (P ^ n)
  ⟩ := by
  induction' n with n ih
  case zero => funext μ; simp
  case succ n ih =>
    funext μ
    simp [ih, smat_as_operator]
    have : P * P ^ n = P ^ 1 * P ^n := by rw [pow_one]
    rw [this]
    simp only [←pow_add]
    have : 1 + n = n + 1 := by ring
    rw [this]

private theorem smat_contraction_in_simplex
  (P : Matrix S S ℝ) [RowStochastic P] [DoeblinMinorization P] :
    ∃ K, 0 < K ∧ ContractingWith K (smat_as_operator P)
  := by
    have hP := (inferInstance : RowStochastic P).stochastic
    obtain ⟨ε, ν, hεpos, hεlt1, hν, h_minorization⟩
      := (inferInstance : DoeblinMinorization P).minorize
    have hnonzero: 1 - ε ≠ 0 := by linarith
    let Q := (1 - ε)⁻¹ • (P - ε • broadcast ν)
    have h_decomp : P = ε • (broadcast ν) + (1 - ε) • Q := by
      unfold Q; simp [hnonzero];
    have hε0 : 0 ≤ 1 - ε := by linarith

    have hQ : RowStochastic Q := by
      constructor; intro i; constructor
      case nonneg =>
        unfold Q
        intro j
        unfold broadcast
        simp
        have hinv_nonneg : 0 ≤ (1 - ε)⁻¹ := by
          exact inv_nonneg.mpr hε0
        have hdiff_nonneg : 0 ≤ P i j - ε * ν j := by
          have := h_minorization i j
          exact sub_nonneg.mpr this
        exact mul_nonneg hinv_nonneg hdiff_nonneg
      case rowsum =>
        unfold Q
        unfold broadcast
        simp
        simp [mul_sub]
        set a := (1 - ε)⁻¹
        calc
          ∑ x, a * P i x - ∑ x, a * (ε * ν x)
        _ = ∑ x, P i x * a - ∑ x, ν x * ε * a := by simp [mul_comm]
        _ = (∑ x, P i x) * a - (∑ x, ν x) * ε * a := by simp [sum_mul]
        _ = a - ε * a := by simp [(hP i).rowsum, hν.rowsum]
        _ = 1 * a - ε * a := by simp
        _ = (1 - ε) * a := by rw [sub_mul]
        _ = 1 := by unfold a; simp [hnonzero]

    let K : ℝ≥0 := ⟨1 - ε, hε0⟩
    refine ⟨?K, ?hKpos, ?hK⟩
    case K => exact K
    case hKpos =>
      unfold K;
      have : 0 < 1 - ε := by linarith
      exact_mod_cast this
    case hK =>
      unfold ContractingWith
      unfold LipschitzWith
      unfold smat_as_operator
      refine ⟨?hKlt1, ?hLip⟩
      case hLip =>
        intro x y
        simp
        have hx_sum : ∑ i, x.val i = 1 := (x.property).2
        have hy_sum : ∑ i, y.val i = 1 := (y.property).2
        have hxB : x.val ᵥ* broadcast ν = ν := by
          funext j
          simp [vecMul_broadcast, hx_sum]
        have hyB : y.val ᵥ* broadcast ν = ν := by
          funext j
          simp [vecMul_broadcast, hy_sum]
        have hxP : x.val ᵥ* P =
          ε • (x.val ᵥ* broadcast ν) + (1 - ε) • (x.val ᵥ* Q) := by
          rw [h_decomp]
          simp [Matrix.vecMul_add, vecMul_smul]
        have hyP : y.val ᵥ* P =
          ε • (y.val ᵥ* broadcast ν) + (1 - ε) • (y.val ᵥ* Q) := by
          rw [h_decomp]
          simp [Matrix.vecMul_add, vecMul_smul]
        have diff_eq :
            (x.val ᵥ* P) - (y.val ᵥ* P)
            = (1 - ε) • ((x.val ᵥ* Q) - (y.val ᵥ* Q)) := by
          calc
            (x.val ᵥ* P) - (y.val ᵥ* P)
          _ = (ε • (x.val ᵥ* broadcast ν) + (1 - ε) • (x.val ᵥ* Q))
              - (ε • (y.val ᵥ* broadcast ν) + (1 - ε) • (y.val ᵥ* Q)) := by
              simp [hxP, hyP]
          _ = ε • ((x.val ᵥ* broadcast ν) - (y.val ᵥ* broadcast ν))
              + (1 - ε) • ((x.val ᵥ* Q) - (y.val ᵥ* Q)) := by
              simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                    sub_eq_add_neg]
          _ = (1 - ε) • ((x.val ᵥ* Q) - (y.val ᵥ* Q)) := by
              simp [hxB, hyB]

        have hxynorm : ‖x.val ᵥ* P - y.val ᵥ* P‖₁
          ≤ K * ‖x.val - y.val‖₁ := by
            have h := congrArg (fun (x : S → ℝ) => ‖x‖₁) diff_eq
            simp at h
            rw [nnnorm_smul] at h
            have : ‖1 - ε‖₊ = K := by rw [Real.nnnorm_of_nonneg hε0]; rfl
            rw [this] at h
            have hLipQ := smat_nonexpansive_in_l1 Q x y
            have := mul_le_mul_of_nonneg_left hLipQ (by positivity : (0 : ℝ≥0) ≤ K)
            simp only [WithLp.toLp_sub] at this ⊢
            rw [h]
            exact this

        have : d₁(x ᵥ* P, y ᵥ* P) ≤ K * d₁(x, y) := by
          calc
            d₁(x ᵥ* P, y ᵥ* P)
          _ = ‖x ᵥ* P  - y ᵥ* P‖₁ := by
            rw [edist_nndist]
            simp [nndist_eq_nnnorm (E := l1Space S)]
          _ ≤ K * ‖x - y‖₁ := by
            refine (ENNReal.coe_le_coe.mpr ?_)
            simpa using hxynorm
          _ = K * d₁(x, y) := by
            simp [edist_nndist, -coe_nnreal_ennreal_nndist]
            simp [←nndist_eq_nnnorm (E := l1Space S) x y]
        exact this
      case hKlt1 =>
        unfold K
        have : 1 - ε < 1 := by linarith
        exact this

end contraction

section stationary_distribution

class Stationary (μ : S → ℝ) (P : Matrix S S ℝ) : Prop where
  stationary : μ ᵥ* P = μ

variable [DecidableEq S]

lemma multi_step_stationary
  (μ : S → ℝ) [StochasticVec μ]
  (P : Matrix S S ℝ) [RowStochastic P]
  (n : ℕ) [Stationary μ P] :
  Stationary μ (P ^ n) := by
  constructor
  induction n with
  | zero =>
    simp [Matrix.vecMul_one]
  | succ n ih =>
    have := (inferInstance : Stationary μ P).stationary
    rw [pow_succ, ←vecMul_vecMul, ih, this]

variable [Nonempty S]

noncomputable abbrev uniform_distribution : S → ℝ := fun _ => 1 / Fintype.card S

instance : StochasticVec (S := S) uniform_distribution := by
  constructor
  case nonneg => intro s; simp [uniform_distribution]
  case rowsum =>
    simp [uniform_distribution, Finset.sum_const, Finset.card_univ]

instance : Nonempty ↑(Simplex S) := by
  simp
  refine ⟨WithLp.toLp 1 (uniform_distribution (S := S)), ?hf⟩
  infer_instance

theorem stationary_distribution_exists (P : Matrix S S ℝ) [RowStochastic P]
  : ∃ μ : S → ℝ, StochasticVec μ ∧ Stationary μ P := by
  letI : DecidableEq S := Classical.decEq S
  have hP := row_stochastic_mem P
  obtain ⟨E, _, seq, hseq, hE, _⟩ :=
    NativePaidHistoryCommonRowLimits.pair_cluster P P hP hP
  have hEs := NativePaidHistoryCommonRowLimits.stochastic_limit _ E
    (fun n => NativePaidHistoryCommonRowLimits.cesaro_stochastic P hP (seq n + 1)
      (Nat.succ_pos _)) hE
  have hfixed := NativePaidHistoryCommonRowLimits.cesaro_fixed P E hP
    (fun n => seq n + 1) ((tendsto_add_atTop_nat 1).comp hseq.tendsto_atTop) hE
  let i : S := Classical.choice inferInstance
  refine ⟨E i, ⟨fun j => Matrix.nonneg_of_mem_rowStochastic hEs,
    Matrix.sum_row_of_mem_rowStochastic hEs i⟩, ⟨?_⟩⟩
  exact congrFun hfixed.2 i

private theorem stationary_distribution_uniquely_exists
  (P : Matrix S S ℝ) [RowStochastic P] [Aperiodic P] [Irreducible P]
  : ∃! μ : S → ℝ, StochasticVec μ ∧ Stationary μ P := by
  obtain ⟨μ, hμ, hμstationary⟩ := stationary_distribution_exists P
  refine ⟨μ, ?hμ, ?huniq⟩
  case hμ => simp; exact ⟨hμ, hμstationary⟩
  case huniq =>
    intro ν hν
    obtain ⟨hν, hνstationary⟩ := hν
    obtain ⟨N, _, hN⟩ := smat_minorizable_with_large_pow P
    let f := smat_as_operator (P ^ N)
    obtain ⟨K, _, hf⟩ := smat_contraction_in_simplex (P ^ N)
    have : IsFixedPt f ⟨μ, by simp [hμ]⟩ := by
      simp [IsFixedPt, f, smat_as_operator]
      exact (multi_step_stationary μ P N).stationary
    have hμfixed := fixedPoint_unique hf this
    have : IsFixedPt f ⟨ν, by simp [hν]⟩ := by
      simp [IsFixedPt, f, smat_as_operator]
      exact (multi_step_stationary ν P N).stationary
    have hνfixed := fixedPoint_unique hf this
    have := hνfixed.trans hμfixed.symm
    simp at this
    exact this

class GeometricMixing
  (P : Matrix S S ℝ) [RowStochastic P]
  : Prop where
  mixing : ∃ (C : ℝ) (ρ : ℝ) (μ : S → ℝ),
    0 < C ∧ 0 < ρ ∧ ρ < 1 ∧ StochasticVec μ ∧ Stationary μ P ∧
    ∀ (x : S → ℝ) [StochasticVec x] (n : ℕ),
      ‖x ᵥ* (P ^ n) - μ‖₁ ≤ C * ρ ^ n

instance geometricMixing (P : Matrix S S ℝ) [RowStochastic P] [Aperiodic P] [Irreducible P]
  : GeometricMixing P := by
  obtain ⟨μ, hμ, hμstationary⟩ := stationary_distribution_exists P
  obtain ⟨N, hNge1, hN⟩ := smat_minorizable_with_large_pow P
  have hNpos : 0 < N := by linarith
  let f := smat_as_operator (P ^ N)
  obtain ⟨K, hKpos, hf⟩ := smat_contraction_in_simplex (P ^ N)
  have : IsFixedPt f ⟨μ, by simp [hμ]⟩ := by
    simp [IsFixedPt, f, smat_as_operator]
    exact (multi_step_stationary μ P N).stationary
  have hμfixed := fixedPoint_unique hf this

  have hKle1 := NNReal.coe_le_coe.mpr hf.1.le
  conv_rhs at hKle1 => simp

  constructor
  refine ⟨?C, ?ρ, ?μ, ?hCpos, ?hρpos, ?hρlt1, ?hμ, ?hμstationary, ?hmixing⟩
  case C => exact 2 / K / (1 - K)
  case ρ => exact K ^ (1 / (N : ℝ))
  case μ => exact μ
  case hCpos =>
    have h₁ : 0 < 1 - (K : ℝ) := by simp [hf.1]
    have h₂ : 0 < 2 / (K : ℝ) := by simp [hKpos]
    apply @_root_.mul_pos
    exact h₂
    simp [h₁]
  case hρpos => apply Real.rpow_pos_of_pos hKpos
  case hρlt1 =>
    have : (K : ℝ) < 1 := by simp [hf.1]
    apply Real.rpow_lt_one
    simp
    simp [hf.1]
    simp [hNpos]
  case hμ => exact hμ
  case hμstationary => exact hμstationary
  case hmixing =>
    intro x₀ hx₀ n
    have hrate := apriori_dist_iterate_fixedPoint_le hf ⟨x₀, hx₀⟩ (n / N)
    rw [←hμfixed] at hrate
    simp [smat_as_operator] at hrate
    rw [smat_as_operator_iter (P ^ N) (n / N)] at hrate
    simp at hrate

    calc
        toReal ‖x₀ ᵥ* P ^ n - μ ‖₁
      _ ≤ toReal ‖x₀ ᵥ* (P ^ N) ^ (n / N) - μ‖₁ := by
        have hPn : P ^ n = (P ^ N) ^ (n / N) * P ^ (n % N) := by
          conv_lhs => rw [←Nat.div_add_mod n N, pow_add, pow_mul]
        conv_lhs =>
          rw [hPn, ←vecMul_vecMul]
          rw [←(multi_step_stationary μ P (n % N)).stationary]
        exact smat_nonexpansive_in_l1 (P ^ (n % N)) (x₀ ᵥ* (P ^ N) ^ (n / N)) μ
      _ ≤ toReal ‖x₀ - x₀ ᵥ* P ^ N‖₁ * K ^ (n / N) / (1 - K) := by
        exact hrate
      _ ≤ 2 * K ^ (n / N) / (1 - K) := by
        have : ‖x₀ - x₀ ᵥ* P ^ N‖₁ ≤ 2 := by calc
            ‖x₀ - x₀ ᵥ* P ^ N‖₁
          _ ≤ ‖x₀‖₁ + ‖x₀ ᵥ* P ^ N‖₁ := by
            exact nnnorm_sub_le (WithLp.toLp 1 x₀) (WithLp.toLp 1 (x₀ ᵥ* P ^ N))
          _ = 1 + 1 := by
            simp [l1_norm_eq_one]
          _ = 2 := by ring
        gcongr
        all_goals try linarith
        exact_mod_cast this
      _ ≤ 2 * K ^ (((n : ℝ) / N) - 1) / (1 - K) := by
        set z : ℕ := n / N
        set z' : ℝ := (n : ℝ) / N
        have : z ≥ z' - 1 := by
          have : n < (z + 1) * N := by calc
              n
            _ = z * N + n % N := (Nat.div_add_mod' n N).symm
            _ < z * N + N := by
              have := Nat.mod_lt n hNpos.gt
              linarith
            _ = (z + 1) * N := by
              simp [Nat.succ_mul, Nat.add_comm]
          have : (n : ℝ) ≤ (z + 1) * (N : ℝ) := by
            exact_mod_cast (Nat.le_of_lt this)
          rw [mul_comm] at this
          have := (div_le_iff₀' (c := (N : ℝ)) (a := (z + 1 : ℝ)) (b := (n : ℝ)) (by exact_mod_cast hNpos)).mpr this
          linarith
        have : (K : ℝ) ^ z ≤ (K : ℝ) ^ (z' - 1) := by
          have := Real.rpow_le_rpow_of_exponent_le_or_ge
            (x := (K : ℝ)) (y := (z : ℝ)) (z := z' - 1) (h := by
            apply Or.inr; refine ⟨hKpos, hKle1, this.le⟩)
          exact_mod_cast this
        gcongr
        all_goals try linarith
      _ = (2 / K / (1 - K)) * (K ^ (1 / (N : ℝ))) ^ n := by
        have := Real.rpow_sub hKpos ((n : ℝ) / N) 1
        simp at this
        rw [this, mul_div_assoc', mul_div_right_comm]
        rw [mul_div_right_comm]
        simp
        apply Or.inl
        rw [div_eq_mul_one_div, mul_comm]
        simp
        rw [Real.rpow_mul (hx := by simp)]
        simp

private theorem primitive_bridge (P : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S) (hprim : Matrix.IsPrimitive P) :
    RowStochastic P ∧
    (letI : RowStochastic P := ⟨fun i =>
      ⟨(Matrix.mem_rowStochastic_iff_sum.mp hP).1 i,
       (Matrix.mem_rowStochastic_iff_sum.mp hP).2 i⟩⟩
     Irreducible P ∧ Aperiodic P) := by
  letI : RowStochastic P := ⟨fun i =>
    ⟨(Matrix.mem_rowStochastic_iff_sum.mp hP).1 i,
     (Matrix.mem_rowStochastic_iff_sum.mp hP).2 i⟩⟩
  refine ⟨inferInstance, ?_⟩
  obtain ⟨k, hkpos, hk⟩ := hprim.exists_pos_pow
  have hnext : ∀ i j, 0 < (P ^ (k + 1)) i j := by
    intro i j
    obtain ⟨t, _, ht⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun t (_ : t ∈ Finset.univ) => hprim.nonneg i t)).mp
        (by rw [Matrix.sum_row_of_mem_rowStochastic hP i]; norm_num)
    change 0 < (P ^ (Nat.succ k)) i j
    rw [_root_.pow_succ', Matrix.mul_apply]
    exact (Finset.sum_pos_iff_of_nonneg
      (fun t _ => mul_nonneg (hprim.nonneg i t)
        (Matrix.pow_apply_nonneg hprim.nonneg k t j))).mpr
          ⟨t, Finset.mem_univ t, mul_pos ht (hk t j)⟩
  refine ⟨⟨fun i j => ⟨k, hk i j⟩⟩, ⟨fun i => ?_⟩⟩
  refine ⟨⟨{k, k+1}, ?_, ?_, ?_, ?_⟩⟩
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact ⟨hkpos, hk i i⟩
    · exact ⟨Nat.succ_pos k, hnext i i⟩
  · simp [Finset.gcd_insert, Finset.gcd_singleton, gcd_eq_nat_gcd, Nat.gcd_self_add_right]
  · simp [ne_of_gt hkpos, (ne_of_gt hkpos).symm]
  · simp

/-- A primitive finite real row-stochastic matrix converges to its unique stationary probability row. -/
theorem primitive_convergence (P : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S) (hprim : Matrix.IsPrimitive P) :
    ∃ μ : S → ℝ, (∀ j, 0 ≤ μ j) ∧ (∑ j, μ j = 1) ∧
      μ ᵥ* P = μ ∧
      (∀ ν : S → ℝ, (∀ j, 0 ≤ ν j) → (∑ j, ν j = 1) → ν ᵥ* P = ν → ν = μ) ∧
      Tendsto (fun n : ℕ => P ^ n) atTop (𝓝 (fun _ j => μ j)) := by
  letI : RowStochastic P := ⟨fun i =>
    ⟨(Matrix.mem_rowStochastic_iff_sum.mp hP).1 i,
     (Matrix.mem_rowStochastic_iff_sum.mp hP).2 i⟩⟩
  obtain ⟨_, hi, ha⟩ := primitive_bridge P hP hprim
  letI := hi
  letI := ha
  obtain ⟨C, ρ, μ, hC, hρ, hρ1, hμ, hstat, hmix⟩ :=
    (inferInstance : GeometricMixing P).mixing
  letI := hμ
  letI := hstat
  refine ⟨μ, hμ.nonneg, hμ.rowsum, hstat.stationary, ?_, ?_⟩
  · intro ν hn hs ht
    have huniq := stationary_distribution_uniquely_exists P
    exact huniq.unique ⟨⟨hn, hs⟩, ⟨ht⟩⟩ ⟨hμ, hstat⟩
  · refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
    let δ : S → ℝ := fun t => if i = t then 1 else 0
    letI : StochasticVec δ := by
      constructor
      · intro t; simp [δ]; split_ifs <;> norm_num
      · simp [δ]
    have hrow (n : ℕ) : δ ᵥ* P ^ n = (P ^ n) i := by
      ext j
      simp [δ, Matrix.vecMul, dotProduct]
    have hbound (n : ℕ) : ‖(P ^ n) i j - μ j‖ ≤ C * ρ ^ n := by
      have hb := hmix δ n
      rw [hrow] at hb
      have he := PiLp.norm_apply_le
        (WithLp.toLp 1 ((P ^ n) i - μ)) j
      exact he.trans (by exact_mod_cast hb)
    have hz : Tendsto (fun n : ℕ => (P ^ n) i j - μ j) atTop (𝓝 0) :=
      squeeze_zero_norm hbound
        (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul C)
    simpa using hz.add_const (μ j)


end stationary_distribution

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteStochasticMixing
