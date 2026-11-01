/- GID: D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup
   generality: G
   mirror-B: D5/B/S3/Quantum/Semigroups/ThresholdSchurSemigroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite real-label threshold Kraus channels and their exponential Schur semigroup. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic

/-! The new content is the explicit complete threshold Kraus construction and the
separating-gap identity used in its finite product and generator. The only public
mathematical theorem is `result`; all adaptation lemmas are consumed on its live
proof path. This is general finite-dimensional analysis (utility: none), not a
finite computation or a new optimizer. The original whole section 34.3 remains
open until its integer physical correspondence and optimum are supplied. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Semigroups.ThresholdSchurSemigroup

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open Matrix
open scoped BigOperators Matrix CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.Elementwise

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Fixed logical-algebra evolution; the real parameter is scale. -/
def evolution (a : S → ℝ) (u : ℝ) (X : Matrix S S ℂ) : Matrix S S ℂ :=
  fun s t => (Real.exp (-u * |a s - a t| / 2) : ℂ) * X s t

private def cutKraus (p : S → Bool) (q : ℝ) : Option Bool → Matrix S S ℂ
  | none => diagonal (fun _ => (Real.sqrt q : ℂ))
  | some b => diagonal (fun s => if p s = b then (Real.sqrt (1-q) : ℂ) else 0)

private theorem cut_channel (p : S → Bool) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ channel : QuantumChannel S S, ∀ X : Matrix S S ℂ,
      CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      fun s t => (if p s = p t then 1 else (q : ℂ)) * X s t := by
  have hs : (Real.sqrt q : ℂ) * (Real.sqrt q : ℂ) = (q : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hq
  have ht : (Real.sqrt (1-q) : ℂ) * (Real.sqrt (1-q) : ℂ) = (1-q : ℝ) := by
    exact_mod_cast Real.mul_self_sqrt (sub_nonneg.mpr hq1)
  push_cast at ht
  have hK : (∑ r, (cutKraus p q r)ᴴ * cutKraus p q r) = 1 := by
    ext s t
    by_cases h : s = t
    · subst t
      cases hp : p s <;>
        simp [cutKraus, Fintype.sum_option, Fintype.sum_bool, hp,
          diagonal_mul_diagonal, hs, ht] <;> push_cast <;> ring
    · simp [cutKraus, Fintype.sum_option, Fintype.sum_bool,
        diagonal_mul_diagonal, h]
  obtain ⟨channel, hchannel⟩ := finite_kraus_quantum_channel (cutKraus p q) hK
  refine ⟨channel, fun X => (hchannel X).trans ?_⟩
  ext s t
  cases hs' : p s <;> cases ht' : p t <;>
    simp [cutKraus, Fintype.sum_option, Fintype.sum_bool,
      Matrix.mul_diagonal, Matrix.diagonal_mul, hs', ht', hs, ht] <;>
    push_cast <;> first
    | linear_combination X s t * hs + X s t * ht
    | linear_combination X s t * hs

private theorem identity_channel :
    ∃ channel : QuantumChannel S S, ∀ X : Matrix S S ℂ,
      CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = X := by
  obtain ⟨channel, hc⟩ := cut_channel (fun _ : S => false) 1 (by norm_num) le_rfl
  exact ⟨channel, by simpa using hc⟩

private theorem product_channel (n : ℕ) (p : Fin n → S → Bool) (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    ∃ channel : QuantumChannel S S, ∀ X : Matrix S S ℂ,
      CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      fun s t => (∏ i, if p i s = p i t then 1 else (q i : ℂ)) * X s t := by
  induction n with
  | zero =>
    obtain ⟨channel, hc⟩ := identity_channel (S := S)
    exact ⟨channel, by simpa using hc⟩
  | succ n ih =>
    obtain ⟨first, hf⟩ := ih (fun i => p i.castSucc) (fun i => q i.castSucc)
      (fun i => hq i.castSucc)
    obtain ⟨last, hl⟩ := cut_channel (p (Fin.last n)) (q (Fin.last n))
      (hq _).1 (hq _).2
    refine ⟨last.comp first, ?_⟩
    intro X
    rw [QuantumChannel.comp_apply]
    have hfirst : first.toCompletelyPositiveMap (CStarMatrix.ofMatrix X) =
        CStarMatrix.ofMatrix (fun s t =>
          (∏ i : Fin n, if p i.castSucc s = p i.castSucc t then 1
            else (q i.castSucc : ℂ)) * X s t) :=
      congrArg CStarMatrix.ofMatrix (hf X)
    rw [hfirst]
    refine (hl _).trans ?_
    ext s t
    simp only [Fin.prod_univ_castSucc]
    ring

private theorem prefix_gap_sum (loss : ℕ → ℝ) (n t : ℕ) (ht : t ≤ n) :
    (∑ i ∈ Finset.range n, if i < t then loss (i+1)-loss i else 0) =
      loss t-loss 0 := by
  rw [← Finset.sum_filter]
  have hf : (Finset.range n).filter (fun i => i < t) = Finset.range t := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hf, Finset.sum_range_sub]

private theorem separating_gap_sum (loss : ℕ → ℝ) (hmono : Monotone loss)
    (n : ℕ) (s t : Fin (n+1)) :
    (∑ i : Fin n, if (decide (s.val ≤ i.val)) = (decide (t.val ≤ i.val))
      then 0 else loss (i.val+1)-loss i.val) = |loss s.val-loss t.val| := by
  have hle (s t : Fin (n+1)) (hst : s ≤ t) :
      (∑ i : Fin n, if (decide (s.val ≤ i.val)) = (decide (t.val ≤ i.val))
        then 0 else loss (i.val+1)-loss i.val) = loss t.val-loss s.val := by
    have he (i : Fin n) :
        (if (decide (s.val ≤ i.val)) = (decide (t.val ≤ i.val))
          then (0 : ℝ) else loss (i.val+1)-loss i.val) =
        (if i.val < t.val then loss (i.val+1)-loss i.val else 0) -
        (if i.val < s.val then loss (i.val+1)-loss i.val else 0) := by
      have hst' : s.val ≤ t.val := hst
      split_ifs <;> simp_all <;> omega
    simp_rw [he]
    rw [Finset.sum_sub_distrib]
    have hp (t : Fin (n+1)) :
        (∑ i : Fin n, if i.val < t.val then loss (i.val+1)-loss i.val else 0) =
          loss t.val-loss 0 := by
      calc
        _ = ∑ i ∈ Finset.range n, if i < t.val then loss (i+1)-loss i else 0 :=
          Fin.sum_univ_eq_sum_range (fun i => if i < t.val then loss (i+1)-loss i else 0) n
        _ = _ := prefix_gap_sum loss n t.val (by omega)
    rw [hp, hp]
    ring
  rcases le_total s t with hst | hts
  · rw [hle s t hst, abs_of_nonpos (sub_nonpos.mpr (hmono hst))]
    ring
  · have he : (∑ i : Fin n, if (decide (s.val ≤ i.val)) =
          (decide (t.val ≤ i.val)) then (0 : ℝ) else loss (i.val+1)-loss i.val) =
        (∑ i : Fin n, if (decide (t.val ≤ i.val)) =
          (decide (s.val ≤ i.val)) then 0 else loss (i.val+1)-loss i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [eq_comm]
    rw [he, hle t s hts, abs_of_nonneg (sub_nonneg.mpr (hmono hts))]

/-- The finite image of the real label function. -/
def labelSet (a : S → ℝ) : Finset ℝ := by
  classical
  exact Finset.univ.image a

/-- Ordered distinct label data; original labels are retained by `rank`. -/
structure ThresholdData (a : S → ℝ) where
  count : ℕ
  loss : ℕ → ℝ
  ordered : Monotone loss
  strictlyOrdered : StrictMono (fun i : Fin (count+1) => loss i.val)
  exactImage : Nonempty S → ∀ i : Fin (count+1), ∃ s, a s = loss i.val
  rank : S → Fin (count+1)
  label_eq : ∀ s, a s = loss (rank s).val
  count_eq : count = (labelSet a).card - 1

private theorem threshold_data_exists (a : S → ℝ) : Nonempty (ThresholdData a) := by
  classical
  let image := labelSet a
  by_cases hn : image.Nonempty
  · obtain ⟨n, hncard⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (Finset.card_pos.mpr hn))
    let e : Fin (n+1) ≃o image := image.orderIsoOfFin hncard
    let loss : ℕ → ℝ := fun i => (e ⟨min i n, by omega⟩).val
    let rank : S → Fin (n+1) := fun s =>
      e.symm ⟨a s, Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩⟩
    refine ⟨⟨n, loss, ?_, ?_, ?_, rank, ?_, ?_⟩⟩
    · intro i j hij
      exact e.monotone (min_le_min_right n hij)
    · intro i j hij
      change (e ⟨min i.val n, _⟩).val < (e ⟨min j.val n, _⟩).val
      apply e.strictMono
      change min i.val n < min j.val n
      rw [min_eq_left (by omega : i.val ≤ n), min_eq_left (by omega : j.val ≤ n)]
      exact hij
    · intro _ i
      have hi := (e ⟨min i.val n, by omega⟩).property
      obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hi
      exact ⟨s, hs⟩
    · intro s
      have hbound : (rank s).val ≤ n := by omega
      change a s = (e ⟨min (rank s).val n, _⟩).val
      have heq : (⟨min (rank s).val n, by omega⟩ : Fin (n+1)) = rank s := by
        apply Fin.ext
        exact min_eq_left hbound
      rw [heq]
      exact congrArg Subtype.val (e.apply_symm_apply
        ⟨a s, Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩⟩).symm
    · change n = image.card - 1
      omega
  · refine ⟨⟨0, fun _ => 0, monotone_const, by intro i j hij; have he : i = j := Fin.ext (by omega); subst j; exact (lt_irrefl _ hij).elim, ?_, fun _ => 0, ?_, ?_⟩⟩
    · intro hs
      obtain ⟨s⟩ := hs
      exact (hn ⟨a s, Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩⟩).elim
    · intro s
      exact (hn ⟨a s, Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩⟩).elim
    · change 0 = image.card - 1
      have hz : image.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
      rw [hz]

/-- Canonical choice of the increasing image of the labels, constant past its end. -/
def thresholds (a : S → ℝ) : ThresholdData a := Classical.choice (threshold_data_exists a)

private theorem channel_exists (a : S → ℝ) (u : ℝ) (hu : 0 ≤ u) :
    ∃ channel : QuantumChannel S S, ∀ X : Matrix S S ℂ,
      CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = evolution a u X := by
  let d := thresholds a
  let p : Fin d.count → S → Bool := fun i s => decide ((d.rank s).val ≤ i.val)
  let q : Fin d.count → ℝ := fun i => Real.exp (-u*(d.loss (i.val+1)-d.loss i.val)/2)
  have hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1 := by
    intro i
    refine ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr ?_⟩
    have h := d.ordered (Nat.le_succ i.val)
    change -u*(d.loss (i.val+1)-d.loss i.val)/2 ≤ 0
    nlinarith [mul_nonneg hu (sub_nonneg.mpr h)]
  obtain ⟨channel, hc⟩ := product_channel d.count p q hq
  refine ⟨channel, fun X => (hc X).trans ?_⟩
  ext s t
  have hfactor (i : Fin d.count) :
      (if p i s = p i t then 1 else (q i : ℂ)) =
      (Real.exp (-u * (if p i s = p i t then 0
        else d.loss (i.val+1)-d.loss i.val) / 2) : ℂ) := by
    split_ifs <;> simp_all [q]
  simp_rw [hfactor]
  rw [← Complex.ofReal_prod, ← Real.exp_sum]
  have he : (∑ i : Fin d.count, -u * (if p i s = p i t then 0
        else d.loss (i.val+1)-d.loss i.val) / 2) = -u * |a s-a t| / 2 := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
    dsimp only [p]
    rw [separating_gap_sum d.loss d.ordered d.count, d.label_eq s, d.label_eq t]
  rw [he]
  rfl


/-- The threshold projection retains exactly the labels at or below its site. -/
def projection (a : S → ℝ) (i : Fin (thresholds a).count) : Matrix S S ℂ :=
  diagonal (fun s => if a s ≤ (thresholds a).loss i.val then 1 else 0)

/-- Adjacent image gaps; an all-equal family has no such indices. -/
def gap (a : S → ℝ) (i : Fin (thresholds a).count) : ℝ :=
  (thresholds a).loss (i.val+1)-(thresholds a).loss i.val

/-- The actual finite threshold Lindblad expression on the logical matrix algebra. -/
def generator (a : S → ℝ) (X : Matrix S S ℂ) : Matrix S S ℂ :=
  ∑ i, (gap a i : ℂ) • (projection a i * X * projection a i -
    (2 : ℂ)⁻¹ • (projection a i * X + X * projection a i))

/-- Matrix-unit coordinates for the generator superoperator. -/
def generatorMatrix (a : S → ℝ) : Matrix (S × S) (S × S) ℂ :=
  diagonal (fun st => (-(|a st.1-a st.2| / 2) : ℝ))

private theorem threshold_iff (a : S → ℝ) (i : Fin (thresholds a).count) (s : S) :
    a s ≤ (thresholds a).loss i.val ↔ ((thresholds a).rank s).val ≤ i.val := by
  rw [(thresholds a).label_eq s]
  change (thresholds a).loss ((thresholds a).rank s).val ≤
    (thresholds a).loss i.castSucc.val ↔ (thresholds a).rank s ≤ i.castSucc
  exact (thresholds a).strictlyOrdered.le_iff_le

private theorem generator_action (a : S → ℝ) (X : Matrix S S ℂ) :
    generator a X = fun s t => (-(|a s-a t| / 2) : ℂ) * X s t := by
  classical
  ext s t
  have hterm (i : Fin (thresholds a).count) :
      ((gap a i : ℂ) • (projection a i * X * projection a i -
        (2 : ℂ)⁻¹ • (projection a i * X + X * projection a i))) s t =
      (-((if (decide (((thresholds a).rank s).val ≤ i.val)) =
          (decide (((thresholds a).rank t).val ≤ i.val))
        then (0 : ℝ) else gap a i) : ℂ)/2) * X s t := by
    simp only [projection, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul,
      threshold_iff]
    by_cases hs : ((thresholds a).rank s).val ≤ i.val <;>
      by_cases ht : ((thresholds a).rank t).val ≤ i.val <;>
      simp [hs, ht] <;> ring <;> simp
  have hreal := separating_gap_sum (thresholds a).loss (thresholds a).ordered
    (thresholds a).count ((thresholds a).rank s) ((thresholds a).rank t)
  rw [← (thresholds a).label_eq s, ← (thresholds a).label_eq t] at hreal
  have hcast : (∑ i : Fin (thresholds a).count,
      if decide (((thresholds a).rank s).val ≤ i.val) =
        decide (((thresholds a).rank t).val ≤ i.val)
      then (0 : ℂ) else (gap a i : ℂ)) = ((|a s-a t| : ℝ) : ℂ) := by
    simpa only [gap, Complex.ofReal_sum, apply_ite, Complex.ofReal_zero]
      using congrArg (fun x : ℝ => (x : ℂ)) hreal
  simp only [generator, Matrix.sum_apply]
  simp_rw [hterm]
  simp only [Complex.ofReal_zero]
  rw [← Finset.sum_mul, ← Finset.sum_div, Finset.sum_neg_distrib, hcast]
  push_cast
  ring

private theorem evolution_add (a : S → ℝ) (u v : ℝ) (X : Matrix S S ℂ) :
    evolution a (u+v) X = evolution a u (evolution a v X) := by
  ext s t
  simp only [evolution]
  rw [show -(u+v)*|a s-a t|/2 = -u*|a s-a t|/2 + -v*|a s-a t|/2 by ring,
    Real.exp_add, Complex.ofReal_mul]
  ring

private theorem evolution_derivative (a : S → ℝ) (X : Matrix S S ℂ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => evolution a v X) (generator a (evolution a u X)) u := by
  rw [generator_action]
  apply hasDerivAt_pi.mpr
  intro s
  apply hasDerivAt_pi.mpr
  intro t
  have h := (((hasDerivAt_id u).neg.mul_const (|a s-a t|)).div_const 2).exp
  have hc := h.ofReal_comp.mul_const (X s t)
  convert hc using 1 <;> simp [evolution] <;> push_cast <;> ring

private theorem evolution_exponential (a : S → ℝ) (u : ℝ) (X : Matrix S S ℂ) :
    (fun st : S × S => evolution a u X st.1 st.2) =
      (NormedSpace.exp (u • generatorMatrix a)).mulVec (fun st => X st.1 st.2) := by
  have hd : u • generatorMatrix a = diagonal
      (fun st : S × S => ((-u*|a st.1-a st.2|/2 : ℝ) : ℂ)) := by
    ext st uv
    by_cases h : st = uv
    · subst uv
      simp [generatorMatrix, Algebra.smul_def]
      push_cast
      ring
    · simp [generatorMatrix, h]
  rw [hd, Matrix.exp_diagonal]
  ext st
  simp only [Matrix.mulVec_diagonal, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, evolution]
  rw [Complex.ofReal_exp]

private theorem channel_ext (f g : QuantumChannel S S)
    (h : ∀ X : Matrix S S ℂ,
      CStarMatrix.ofMatrix.symm (f.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      CStarMatrix.ofMatrix.symm (g.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      congr 1
      apply DFunLike.ext
      intro X
      exact congrArg CStarMatrix.ofMatrix (h (CStarMatrix.ofMatrix.symm X))

/-- Arbitrary finite real labels produce actual CPTP channels, a continuous
scale semigroup, and the threshold generator with its exact matrix exponential.
All matrices, zero scale, repeated labels and the empty threshold family remain
in scope. The exponential uses the matrix-unit basis indexed by `S × S`. -/
theorem result (a : S → ℝ) :
    ∃ channels : {u : ℝ // 0 ≤ u} → QuantumChannel S S,
      (∀ u X, CStarMatrix.ofMatrix.symm
        ((channels u).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        evolution a u.val X) ∧
      (∀ (u v : {u : ℝ // 0 ≤ u}), channels ⟨u.val+v.val, add_nonneg u.property v.property⟩ =
        (channels u).comp (channels v)) ∧
      ((channels ⟨0, le_rfl⟩).toCompletelyPositiveMap.toLinearMap = LinearMap.id) ∧
      (∀ X, evolution a 0 X = X) ∧
      (∀ X, Continuous (fun u : ℝ => evolution a u X)) ∧
      (∀ i, 0 ≤ gap a i ∧ (projection a i)ᴴ = projection a i ∧
        projection a i * projection a i = projection a i) ∧
      (∀ X, generator a X = fun s t => (-(|a s-a t|/2) : ℂ) * X s t) ∧
      (∀ s t, generator a (Matrix.single s t 1) =
        (-(|a s-a t|/2) : ℂ) • Matrix.single s t 1) ∧
      (∀ u X, (fun st : S × S => evolution a u X st.1 st.2) =
        (NormedSpace.exp (u • generatorMatrix a)).mulVec (fun st => X st.1 st.2)) ∧
      (∀ u X, HasDerivAt (fun v : ℝ => evolution a v X)
        (generator a (evolution a u X)) u) := by
  classical
  choose channels hc using fun u : {u : ℝ // 0 ≤ u} => channel_exists a u.val u.property
  refine ⟨channels, hc, ?_, ?_, ?_, ?_, ?_, generator_action a, ?_,
    evolution_exponential a, fun u X => evolution_derivative a X u⟩
  · intro u v
    apply channel_ext
    intro X
    rw [hc, evolution_add, QuantumChannel.comp_apply]
    have hv : (channels v).toCompletelyPositiveMap (CStarMatrix.ofMatrix X) =
        CStarMatrix.ofMatrix (evolution a v.val X) := by
      simpa only [Equiv.apply_symm_apply] using congrArg CStarMatrix.ofMatrix (hc v X)
    rw [hv, hc]
  · apply LinearMap.ext
    intro X
    change (channels ⟨0, le_rfl⟩).toCompletelyPositiveMap X = X
    have h := hc ⟨0, le_rfl⟩ (CStarMatrix.ofMatrix.symm X)
    have hz : evolution a 0 (CStarMatrix.ofMatrix.symm X) =
        CStarMatrix.ofMatrix.symm X := by
      ext s t
      simp [evolution]
    apply CStarMatrix.ofMatrix.symm.injective
    simpa only [Equiv.apply_symm_apply] using h.trans hz
  · intro X
    ext s t
    simp [evolution]
  · intro X
    exact continuous_iff_continuousAt.mpr (fun u => (evolution_derivative a X u).continuousAt)
  · intro i
    refine ⟨sub_nonneg.mpr ((thresholds a).ordered (Nat.le_succ i.val)), ?_, ?_⟩
    · ext s t
      by_cases h : s = t
      · subst t
        simp [projection, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
      · simp [projection, Matrix.conjTranspose_apply, Matrix.diagonal_apply, h, Ne.symm h]
    · rw [projection, Matrix.diagonal_mul_diagonal]
      congr 1
      ext s
      split_ifs <;> norm_num
  · intro s t
    rw [generator_action]
    ext i j
    by_cases hi : s=i <;> by_cases hj : t=j <;> simp [Matrix.single, hi, hj]

#print axioms result

end D5.S3.Quantum.Semigroups.ThresholdSchurSemigroup
