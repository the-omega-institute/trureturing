/- GID: D5/S3/QuantumContext/HanceTwentyFourCellThreshold
   generality: I
   mirror-B: D5/B/S3/QuantumContext/HanceTwentyFourCellThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full noisy twenty-four-cell preparation scenario has exact noncontextuality threshold one half. -/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic

set_option maxRecDepth 8192
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace D5.S3.QuantumContext.HanceTwentyFourCellThreshold
abbrev Signs := Bool × Bool × Bool × Bool
abbrev Vertex := (Fin 4 × Bool) ⊕ Signs
abbrev Question := Fin 4 ⊕ (Bool × Bool × Bool)
def sign (b : Bool) : ℝ := if b then 1 else -1
def bits (s : Signs) : Fin 4 → Bool := ![s.1, s.2.1, s.2.2.1, s.2.2.2]
def vertex : Vertex → Fin 4 → ℝ
  | .inl (i,b), j => if i = j then sign b else 0
  | .inr s, j => sign (bits s j) / 2
def question : Question → Fin 4 → ℝ
  | .inl i, j => if i = j then 1 else 0
  | .inr s, j => ![(1:ℝ)/2, sign s.1/2, sign s.2.1/2, sign s.2.2/2] j
def dot (x y : Fin 4 → ℝ) : ℝ := ∑ i, x i * y i
def statistics (lambda : ℝ) (α : Vertex → ℝ≥0) (n : Question) (b : Bool) : ℝ :=
  ∑ x, (α x : ℝ) * ((1 + sign b * lambda * dot (question n) (vertex x))/2)
def mixture {Ω : Type*} [MeasurableSpace Ω] (α : Vertex → ℝ≥0)
    (μ : Vertex → Measure Ω) : Measure Ω := ∑ x, (α x : ℝ≥0∞) • μ x
structure Model (lambda : ℝ) (Ω : Type*) [MeasurableSpace Ω] where
  preparation : Vertex → Measure Ω
  probability : ∀ x, IsProbabilityMeasure (preparation x)
  response : Question → Bool → Ω → ℝ
  measurable : ∀ n b, Measurable (response n b)
  nonnegative : ∀ n b ω, 0 ≤ response n b ω
  normalized : ∀ n ω, response n true ω + response n false ω = 1
  reproduce : ∀ x n b, ∫ ω, response n b ω ∂preparation x =
    (1 + sign b * lambda * dot (question n) (vertex x))/2
  noncontextual : ∀ α β : Vertex → ℝ≥0, (∑ x, α x) = 1 → (∑ x, β x) = 1 →
    (∀ n b, statistics lambda α n b = statistics lambda β n b) →
    mixture α preparation = mixture β preparation

def admissible.{u} (lambda : ℝ) : Prop :=
  ∃ (Ω : Type u) (m : MeasurableSpace Ω), Nonempty (@Model lambda Ω m)

def anti (s : Signs) : Signs := (!s.1, !s.2.1, !s.2.2.1, !s.2.2.2)
def zeroWeights : Vertex → ℝ≥0
  | .inl (i,_b) => if i = 0 then 1/2 else 0
  | .inr _ => 0
def boundWeights (s : Signs) : Vertex → ℝ≥0
  | .inl (i,b) => if b = bits s i then 1/6 else 0
  | .inr t => if t = anti s then 1/3 else 0

abbrev Ontic := Fin 6 × Bool × Bool
def pairs : Fin 6 → Fin 4 × Fin 4 := ![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def ontic (u : Ontic) (j : Fin 4) : ℝ :=
  (if (pairs u.1).1 = j then sign u.2.1 else 0) +
  (if (pairs u.1).2 = j then sign u.2.2 else 0)
def weight (lambda : ℝ) (x : Vertex) (u : Ontic) : ℝ :=
  (1 + 2 * lambda * dot (ontic u) (vertex x))/24
def onticResponse (n : Question) (b : Bool) (u : Ontic) : ℝ :=
  (1 + sign b * dot (ontic u) (question n))/2

set_option maxHeartbeats 5000000 in
theorem result.{u} (lambda : ℝ) (hLambda : lambda ∈ Set.Icc (0 : ℝ) 1) :
    admissible.{u} lambda ↔ lambda ≤ 1/2 := by
  classical
  constructor
  · rintro ⟨Ω, m, ⟨M⟩⟩
    letI := m
    classical
    letI (x : Vertex) : IsProbabilityMeasure (M.preparation x) := M.probability x
    have upper (n : Question) (b : Bool) (ω : Ω) : M.response n b ω ≤ 1 := by
      have hn := M.normalized n ω
      have hp := M.nonnegative n true ω
      have hm := M.nonnegative n false ω
      cases b <;> linarith
    have int {f : Ω → ℝ} (hm : Measurable f) (hn : ∀ ω, 0 ≤ f ω) (hu : ∀ ω, f ω ≤ 1)
        (x : Vertex) : Integrable f (M.preparation x) := by
      exact (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => by simpa [Real.norm_eq_abs, abs_of_nonneg (hn ω)] using hu ω))
    let w (s : Signs) (ω : Ω) : ℝ :=
      M.response (.inl 0) s.1 ω * M.response (.inl 1) s.2.1 ω *
        M.response (.inl 2) s.2.2.1 ω * M.response (.inl 3) s.2.2.2 ω
    have wm (s : Signs) : Measurable (w s) := by
      exact (((M.measurable _ _).mul (M.measurable _ _)).mul (M.measurable _ _)).mul (M.measurable _ _)
    have wn (s : Signs) (ω : Ω) : 0 ≤ w s ω := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (M.nonnegative _ _ _) (M.nonnegative _ _ _))
        (M.nonnegative _ _ _)) (M.nonnegative _ _ _)
    have wu (s : Signs) (ω : Ω) : w s ω ≤ 1 := by
      dsimp [w]
      have h01 : M.response (.inl 0) s.1 ω * M.response (.inl 1) s.2.1 ω ≤ 1 :=
        mul_le_one₀ (upper _ _ _) (M.nonnegative _ _ _) (upper _ _ _)
      have h012 : M.response (.inl 0) s.1 ω * M.response (.inl 1) s.2.1 ω *
          M.response (.inl 2) s.2.2.1 ω ≤ 1 :=
        mul_le_one₀ h01 (M.nonnegative _ _ _) (upper _ _ _)
      exact mul_le_one₀ h012 (M.nonnegative _ _ _) (upper _ _ _)
    have wi (s : Signs) (x : Vertex) : Integrable (w s) (M.preparation x) := int (wm s) (wn s) (wu s) x
    have wint (α : Vertex → ℝ≥0) (s : Signs) :
        (∫ ω, w s ω ∂mixture α M.preparation) = ∑ x, (α x : ℝ) * ∫ ω, w s ω ∂M.preparation x := by
      unfold mixture
      rw [integral_finsetSum_measure (μ := fun x => (α x : ℝ≥0∞) • M.preparation x)
        (s := Finset.univ) (fun x _ => (wi s x).smul_measure_nnreal)]
      simp only [integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul]
    have bw (s : Signs) : (∑ x, boundWeights s x) = 1 := by
      rcases s with ⟨a,b,c,d⟩
      cases a <;> cases b <;> cases c <;> cases d <;>
        norm_num [boundWeights, bits, anti, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
    have zw : (∑ x, zeroWeights x) = 1 := by
      norm_num [zeroWeights, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
    have eqop (s : Signs) (n : Question) (b : Bool) :
        statistics lambda (boundWeights s) n b = statistics lambda zeroWeights n b := by
      rcases s with ⟨a,c,d,e⟩
      cases a <;> cases c <;> cases d <;> cases e <;> cases b <;>
        simp [statistics, boundWeights, zeroWeights, bits, anti, dot, vertex,
          Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ, sign] <;> ring
    have eqint (s : Signs) :
        (1/6:ℝ) * (∑ i : Fin 4, ∫ ω, w s ω ∂M.preparation (.inl (i, bits s i))) +
        (1/3:ℝ) * (∫ ω, w s ω ∂M.preparation (.inr (anti s))) =
        (1/2:ℝ) * ((∫ ω, w s ω ∂M.preparation (.inl (0,true))) +
          ∫ ω, w s ω ∂M.preparation (.inl (0,false))) := by
      have h := congrArg (fun μ : Measure Ω => ∫ ω, w s ω ∂μ)
        (M.noncontextual (boundWeights s) zeroWeights (bw s) zw (eqop s))
      rw [wint, wint] at h
      rcases s with ⟨a,b,c,d⟩
      cases a <;> cases b <;> cases c <;> cases d <;>
        simp [boundWeights, zeroWeights, bits, anti, Fintype.sum_sum_type, Fintype.sum_prod_type,
          Fintype.sum_bool, Fin.sum_univ_succ] at h ⊢ <;> linarith
    have sumw (ω : Ω) : ∑ s, w s ω = 1 := by
      calc
        _ = (M.response (.inl 0) true ω + M.response (.inl 0) false ω) *
          (M.response (.inl 1) true ω + M.response (.inl 1) false ω) *
          (M.response (.inl 2) true ω + M.response (.inl 2) false ω) *
          (M.response (.inl 3) true ω + M.response (.inl 3) false ω) := by
            simp [w, Fintype.sum_prod_type, Fintype.sum_bool]; ring
        _ = 1 := by rw [M.normalized, M.normalized, M.normalized, M.normalized]; norm_num
    have marg (i : Fin 4) (b : Bool) (ω : Ω) :
        ∑ s : Signs, (if bits s i = b then w s ω else 0) = M.response (.inl i) b ω := by
      have hn (j : Fin 4) : M.response (.inl j) false ω = 1 - M.response (.inl j) true ω := by
        linarith [M.normalized (.inl j) ω]
      fin_cases i <;> cases b <;>
        simp [bits, w, Fintype.sum_prod_type, Fintype.sum_bool, hn] <;> ring
    have margint (i : Fin 4) :
        (∑ s : Signs, ∫ ω, w s ω ∂M.preparation (.inl (i,bits s i))) = 1 + lambda := by
      have ht (b : Bool) :
          (∑ s : Signs, if bits s i = b then ∫ ω, w s ω ∂M.preparation (.inl (i,b)) else 0) =
          ∫ ω, M.response (.inl i) b ω ∂M.preparation (.inl (i,b)) := by
        calc
          _ = ∑ s : Signs, ∫ ω, (if bits s i = b then w s ω else 0) ∂M.preparation (.inl (i,b)) := by
            apply Finset.sum_congr rfl
            intro s _
            by_cases h : bits s i = b <;> simp [h]
          _ = ∫ ω, (∑ s : Signs, if bits s i = b then w s ω else 0) ∂M.preparation (.inl (i,b)) := by
            apply (integral_finsetSum Finset.univ _).symm
            intro s _
            by_cases h : bits s i = b <;> simp [h, wi]
          _ = _ := integral_congr_ae (Filter.Eventually.of_forall (marg i b))
      have hsplit :
          (∑ s : Signs, ∫ ω, w s ω ∂M.preparation (.inl (i,bits s i))) =
          (∑ s : Signs, if bits s i = true then ∫ ω, w s ω ∂M.preparation (.inl (i,true)) else 0) +
          (∑ s : Signs, if bits s i = false then ∫ ω, w s ω ∂M.preparation (.inl (i,false)) else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro s _
        cases h : bits s i <;> simp [h]
      rw [hsplit, ht true, ht false, M.reproduce, M.reproduce]
      simp [dot, vertex, question, sign]
    have sumwi (x : Vertex) : (∑ s, ∫ ω, w s ω ∂M.preparation x) = 1 := by
      rw [← integral_finsetSum Finset.univ (fun s _ => wi s x)]
      simp [sumw, Measure.real]
    have hineq (s : Signs) :
        (1/6:ℝ) * (∑ i : Fin 4, ∫ ω, w s ω ∂M.preparation (.inl (i,bits s i))) ≤
        (1/2:ℝ) * ((∫ ω, w s ω ∂M.preparation (.inl (0,true))) +
          ∫ ω, w s ω ∂M.preparation (.inl (0,false))) := by
      have hn : 0 ≤ ∫ ω, w s ω ∂M.preparation (.inr (anti s)) := integral_nonneg (wn s)
      linarith [eqint s]
    have htotal := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hineq s)
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, sumwi] at htotal
    rw [Finset.sum_comm] at htotal
    simp only [margint, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htotal
    linarith
  · intro hhalf
    have h0 := hLambda.1
    have hb (u : Ontic) (x : Vertex) : -1 ≤ dot (ontic u) (vertex x) ∧ dot (ontic u) (vertex x) ≤ 1 := by
      rcases u with ⟨k,a,b⟩
      fin_cases k <;> cases a <;> cases b <;> rcases x with ⟨i,c⟩ | ⟨c,d,e,f⟩
      all_goals first
        | (fin_cases i <;> cases c <;> norm_num [dot, ontic, pairs, vertex, sign, bits, Fin.sum_univ_four, Fin.sum_univ_six, Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceFinMk])
        | (cases c <;> cases d <;> cases e <;> cases f <;> norm_num [dot, ontic, pairs, vertex, sign, bits, Fin.sum_univ_four, Fin.sum_univ_six, Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceFinMk])
      all_goals
        simp only [Fin.ext_iff, Fin.val_natCast, Fin.coe_ofNat_eq_mod]
        norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceFinMk]
    have hw (x : Vertex) : ∑ u, weight lambda x u = 1 := by
      simp [weight, dot, ontic, pairs, sign, Fin.sum_univ_four, Fin.sum_univ_six, Fintype.sum_prod_type, Fintype.sum_bool]
      ring
    have hs (x : Vertex) (n : Question) (b : Bool) :
        ∑ u, weight lambda x u * onticResponse n b u = (1 + sign b * lambda * dot (question n) (vertex x))/2 := by
      cases b <;> simp [weight, onticResponse, dot, ontic, pairs, Fin.sum_univ_four, Fin.sum_univ_six, Fintype.sum_prod_type, Fintype.sum_bool, sign, Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceFinMk] <;> ring
    classical
    let Ω := ULift.{u} Ontic
    letI : MeasurableSpace Ω := ⊤
    letI : MeasurableSingletonClass Ω := ⟨fun _ => trivial⟩
    have wp (x : Vertex) (u : Ontic) : 0 ≤ weight lambda x u := by
      have h := hb u x
      have hprod := mul_nonneg (show 0 ≤ 2*lambda by linarith) (show 0 ≤ dot (ontic u) (vertex x) + 1 by linarith)
      dsimp [weight]
      linarith
    let μ (x : Vertex) : Measure Ω := Measure.sum (fun u : Ontic =>
      ENNReal.ofReal (weight lambda x u) • Measure.dirac (ULift.up u))
    have mp (x : Vertex) : IsProbabilityMeasure (μ x) := by
      constructor
      simp only [μ, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one, tsum_fintype]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun u _ => wp x u), hw]
      norm_num
    let ξ (n : Question) (b : Bool) (ω : Ω) : ℝ := onticResponse n b ω.down
    have rb (n : Question) (u : Ontic) : -1 ≤ dot (ontic u) (question n) ∧ dot (ontic u) (question n) ≤ 1 := by
      rcases n with i | ⟨a,b,c⟩
      · exact hb u (.inl (i,true))
      · have qeq : question (.inr (a,b,c)) = vertex (.inr (true,a,b,c)) := by
          funext j
          fin_cases j <;> rfl
        rw [qeq]
        exact hb u (.inr (true,a,b,c))
    refine ⟨Ω, inferInstance, ⟨{
      preparation := μ
      probability := mp
      response := ξ
      measurable := fun n b => measurable_of_finite _
      nonnegative := ?_
      normalized := ?_
      reproduce := ?_
      noncontextual := ?_ }⟩⟩
    · intro n b ω
      have h := rb n ω.down
      cases b <;> simp [ξ, onticResponse, sign] <;> linarith
    · intro n ω
      simp [ξ, onticResponse, sign]
      ring
    · intro x n b
      dsimp [μ]
      rw [integral_sum_dirac (fun u => ENNReal.ofReal_ne_top)]
      simp only [tsum_fintype, ENNReal.toReal_ofReal (wp x _), smul_eq_mul, ξ]
      exact hs x n b
    · intro α β hα hβ heq
      have stat (γ : Vertex → ℝ≥0) (hγ : ∑ x, γ x = 1) (i : Fin 4) :
          statistics lambda γ (.inl i) true = (1 + lambda * ∑ x, (γ x : ℝ) * vertex x i)/2 := by
        have hn : ∑ x, (γ x : ℝ) = 1 := by exact_mod_cast hγ
        have hd (x : Vertex) : dot (question (.inl i)) (vertex x) = vertex x i := by
          simp [dot, question, ite_mul]
        calc
          _ = ∑ x, ((γ x : ℝ)/2 + (lambda/2)*((γ x : ℝ)*vertex x i)) := by
            unfold statistics
            apply Finset.sum_congr rfl
            intro x _
            rw [hd]
            simp only [sign, ite_true]
            ring
          _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, hn]; ring
      have coords (i : Fin 4) :
          lambda * (∑ x, (α x : ℝ) * vertex x i) = lambda * (∑ x, (β x : ℝ) * vertex x i) := by
        have hc := heq (.inl i) true
        rw [stat α hα, stat β hβ] at hc
        linarith
      have affine (γ : Vertex → ℝ≥0) (hγ : ∑ x, γ x = 1) (u : Ontic) :
          (∑ x, (γ x : ℝ) * weight lambda x u) =
            1/24 + ∑ i : Fin 4, (ontic u i / 12) * (lambda * ∑ x, (γ x : ℝ) * vertex x i) := by
        have hn : ∑ x, (γ x : ℝ) = 1 := by exact_mod_cast hγ
        calc
          _ = ∑ x, ((γ x : ℝ)/24 + ∑ i : Fin 4, (ontic u i / 12) * (lambda * ((γ x : ℝ)*vertex x i))) := by
            apply Finset.sum_congr rfl
            intro x _
            simp only [weight, dot, Fin.sum_univ_four]
            ring
          _ = _ := by
            rw [Finset.sum_add_distrib, ← Finset.sum_div, hn, Finset.sum_comm]
            simp only [← Finset.mul_sum]
      have weights (u : Ontic) :
          (∑ x, (α x : ℝ) * weight lambda x u) = ∑ x, (β x : ℝ) * weight lambda x u := by
        rw [affine α hα, affine β hβ]
        simp only [coords]
      have coeffs (u : Ontic) :
          (∑ x, (α x : ℝ≥0∞) * ENNReal.ofReal (weight lambda x u)) =
            ∑ x, (β x : ℝ≥0∞) * ENNReal.ofReal (weight lambda x u) := by
        simp_rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (NNReal.coe_nonneg _) (wp x u)),
          ← ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (NNReal.coe_nonneg _) (wp x u)), weights]
      ext A hA
      simp only [mixture, μ, Measure.finsetSum_apply, Measure.smul_apply, Measure.sum_apply _ hA, tsum_fintype, smul_eq_mul]
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm, Finset.sum_comm (f := fun x u => (β x : ℝ≥0∞) * ENNReal.ofReal (weight lambda x u) * Measure.dirac (ULift.up u) A)]
      simp_rw [← Finset.sum_mul, coeffs]
end D5.S3.QuantumContext.HanceTwentyFourCellThreshold
#print axioms D5.S3.QuantumContext.HanceTwentyFourCellThreshold.result
