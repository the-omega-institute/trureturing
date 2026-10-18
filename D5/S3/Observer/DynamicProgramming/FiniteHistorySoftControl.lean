/- GID: D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl
   generality: G
   mirror-B: D5/B/S3/Observer/DynamicProgramming/FiniteHistorySoftControl
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Candidate on the actual supported path and all-history policy laws. -/
import D5.S3.Divergence.GrandmotherTheorem
import D5.S3.Divergence.GibbsEquality
import D5.S3.DivergenceSupport.ZeroSupportDPI

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
open scoped BigOperators
open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.GrandmotherTheorem
namespace FiniteHistorySoftControl
universe u
variable {X : Type u} [Fintype X]
structure Model (X : Type u) [Fintype X] where
  R : X → X → ℝ
  nonneg : ∀ x y, 0 ≤ R x y
  stochastic : ∀ x, ∑ y, R x y = 1
  c : X → X → ℝ
  g : X → ℝ
  τ : ℝ
  temperature : 0 < τ
abbrev Succ (M : Model X) (x : X) := {y : X // 0 < M.R x y}
instance (M : Model X) (x : X) : Fintype (Succ M x) := Fintype.ofFinite _
def Prob {A : Type*} [Fintype A] (p : A → ℝ) : Prop := (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1
namespace Model
variable (M : Model X)
def Path : ℕ → X → Type u
  | 0, _ => PUnit
  | n+1, x => Σ y : Succ M x, Path n y.val
@[instance_reducible] noncomputable def pathFintype : (n : ℕ) → (x : X) → Fintype (M.Path n x)
  | 0, _ => inferInstanceAs (Fintype PUnit)
  | n+1, x => by
    letI : ∀ y : Succ M x, Fintype (M.Path n y.val) := fun y => pathFintype n y.val
    exact inferInstanceAs (Fintype (Σ y : Succ M x, M.Path n y.val))
instance (n : ℕ) (x : X) : Fintype (M.Path n x) := M.pathFintype n x
/-- The actual custom finite path space at horizon zero has its unique empty history. -/
lemma path_nonempty (n : ℕ) (x : X) : Nonempty (M.Path n x) := by
  have support_sum (x : X) : ∑ y : Succ M x, M.R x y.val = 1 := by
    classical
    have hs : (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : Succ M x, M.R x y.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    rw [← hs]
    calc
      (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : X, M.R x y := by
        apply Finset.sum_congr rfl
        intro y _
        split_ifs with h
        · rfl
        · exact (le_antisymm (le_of_not_gt h) (M.nonneg x y)).symm
      _ = 1 := M.stochastic x
  have support_nonempty (x : X) : Nonempty (Succ M x) := by
    classical
    by_contra h
    haveI : IsEmpty (Succ M x) := not_nonempty_iff.mp h
    have := support_sum x
    simp at this
  induction n generalizing x with
  | zero => exact ⟨PUnit.unit⟩
  | succ n ih =>
    obtain ⟨y⟩ := support_nonempty x
    obtain ⟨w⟩ := ih y.val
    exact ⟨⟨y,w⟩⟩
structure Row (x : X) where
  q : Succ M x → ℝ
  prob : Prob q
/-- A full rooted policy tree: a separate continuation after every supported successor.
Its quantifier includes every finite history-dependent policy, including unreachable histories. -/
def Policy : ℕ → X → Type u
  | 0, _ => PUnit
  | n+1, x => M.Row x × ((y : Succ M x) → Policy n y.val)
def reference : (n : ℕ) → (x : X) → M.Path n x → ℝ
  | 0, _, _ => 1
  | n+1, x, w => M.R x w.1.val * reference n w.1.val w.2
def cost : (n : ℕ) → (x : X) → M.Path n x → ℝ
  | 0, x, _ => M.g x
  | n+1, x, w => M.c x w.1.val + cost n w.1.val w.2
def law : (n : ℕ) → (x : X) → M.Policy n x → M.Path n x → ℝ
  | 0, _, _, _ => 1
  | n+1, _, π, w => π.1.q w.1 * law n w.1.val (π.2 w.1) w.2
def conditionalKL : (n : ℕ) → (x : X) → M.Policy n x → ℝ
  | 0, _, _ => 0
  | n+1, x, π => klDivergence π.1.q (fun y => M.R x y.val) + ∑ y, π.1.q y * conditionalKL n y.val (π.2 y)
def J (n : ℕ) (x : X) (π : M.Policy n x) : ℝ := (∑ w, M.law n x π w * M.cost n x w) +
    M.τ * klDivergence (M.law n x π) (M.reference n x)
lemma reference_pos (n : ℕ) (x : X) (w : M.Path n x) : 0 < M.reference n x w := by
  induction n generalizing x with
  | zero => exact zero_lt_one
  | succ n ih => exact mul_pos w.1.property (ih w.1.val w.2)
lemma law_prob (n : ℕ) (x : X) (π : M.Policy n x) : Prob (M.law n x π) := by
  have path_sum_step (n : ℕ) (x : X) (f : M.Path (n+1) x → ℝ) :
      (∑ w, f w) = ∑ y : Succ M x, ∑ w : M.Path n y.val, f ⟨y,w⟩ := by
    change (∑ w : Σ y : Succ M x, M.Path n y.val, f w) = _
    exact Fintype.sum_sigma _
  have path_sum_zero (x : X) (f : M.Path 0 x → ℝ) : (∑ w, f w) = f PUnit.unit := by
    classical
    refine Finset.sum_eq_single (PUnit.unit : M.Path 0 x) ?_ ?_
    · intro w _ hw
      exact (hw (Subsingleton.elim _ _)).elim
    · intro h
      exact (h (Finset.mem_univ _)).elim
  induction n generalizing x with
  | zero =>
    constructor
    · intro w; exact zero_le_one
    · change (∑ w : M.Path 0 x, (1 : ℝ)) = 1
      exact path_sum_zero x (fun _ => 1)
  | succ n ih =>
    constructor
    · intro w; exact mul_nonneg (π.1.prob.1 w.1) ((ih _ (π.2 w.1)).1 w.2)
    · simp only [path_sum_step, law, ← Finset.mul_sum]
      simpa only [fun y => (ih y.val (π.2 y)).2, mul_one] using π.1.prob.2
lemma reference_prob (n : ℕ) (x : X) : Prob (M.reference n x) := by
  have path_sum_step (n : ℕ) (x : X) (f : M.Path (n+1) x → ℝ) :
      (∑ w, f w) = ∑ y : Succ M x, ∑ w : M.Path n y.val, f ⟨y,w⟩ := by
    change (∑ w : Σ y : Succ M x, M.Path n y.val, f w) = _
    exact Fintype.sum_sigma _
  have path_sum_zero (x : X) (f : M.Path 0 x → ℝ) : (∑ w, f w) = f PUnit.unit := by
    classical
    refine Finset.sum_eq_single (PUnit.unit : M.Path 0 x) ?_ ?_
    · intro w _ hw
      exact (hw (Subsingleton.elim _ _)).elim
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have support_sum (x : X) : ∑ y : Succ M x, M.R x y.val = 1 := by
    classical
    have hs : (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : Succ M x, M.R x y.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    rw [← hs]
    calc
      (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : X, M.R x y := by
        apply Finset.sum_congr rfl
        intro y _
        split_ifs with h
        · rfl
        · exact (le_antisymm (le_of_not_gt h) (M.nonneg x y)).symm
      _ = 1 := M.stochastic x
  induction n generalizing x with
  | zero =>
    constructor
    · intro w; exact zero_le_one
    · change (∑ w : M.Path 0 x, (1 : ℝ)) = 1
      exact path_sum_zero x (fun _ => 1)
  | succ n ih =>
    constructor
    · intro w; exact (M.reference_pos (n+1) x w).le
    · simp only [path_sum_step, reference, ← Finset.mul_sum]
      simpa only [fun (y : Succ M x) => (ih y.val).2, mul_one] using support_sum x
/-- The original reference rows at every history, also used to complete zero histories. -/
def referencePolicy : (n : ℕ) → (x : X) → M.Policy n x
  | 0, _ => PUnit.unit
  | n+1, x => by
    have support_sum (x : X) : ∑ y : Succ M x, M.R x y.val = 1 := by
      classical
      have hs : (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : Succ M x, M.R x y.val := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype _ (by simp) _
      rw [← hs]
      calc
        (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : X, M.R x y := by
          apply Finset.sum_congr rfl
          intro y _
          split_ifs with h
          · rfl
          · exact (le_antisymm (le_of_not_gt h) (M.nonneg x y)).symm
        _ = 1 := M.stochastic x
    exact (⟨(fun y => M.R x y.val),
          ⟨(fun y => y.property.le), support_sum x⟩⟩, fun y => referencePolicy n y.val)
lemma referencePolicy_law (n : ℕ) (x : X) : M.law n x (M.referencePolicy n x) = M.reference n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    funext w
    change M.R x w.1.val * M.law n w.1.val (M.referencePolicy n w.1.val) w.2 =
      M.R x w.1.val * M.reference n w.1.val w.2
    rw [ih w.1.val]

/-- Every probability law on the entire feasible path space is a history policy law.
At a zero-mass history the conditional law is completed with the original R law. -/
lemma law_factorization (n : ℕ) (x : X) (p : M.Path n x → ℝ) (hp : Prob p) :
    ∃ π : M.Policy n x, M.law n x π = p := by
  have path_sum_step (n : ℕ) (x : X) (f : M.Path (n+1) x → ℝ) :
      (∑ w, f w) = ∑ y : Succ M x, ∑ w : M.Path n y.val, f ⟨y,w⟩ := by
    change (∑ w : Σ y : Succ M x, M.Path n y.val, f w) = _
    exact Fintype.sum_sigma _
  have path_sum_zero (x : X) (f : M.Path 0 x → ℝ) : (∑ w, f w) = f PUnit.unit := by
    classical
    refine Finset.sum_eq_single (PUnit.unit : M.Path 0 x) ?_ ?_
    · intro w _ hw
      exact (hw (Subsingleton.elim _ _)).elim
    · intro h
      exact (h (Finset.mem_univ _)).elim
  classical
  induction n generalizing x with
  | zero =>
    refine ⟨PUnit.unit, ?_⟩
    funext w
    have hs := hp.2
    rw [path_sum_zero] at hs
    have hw : w = (PUnit.unit : M.Path 0 x) := by
      exact @Subsingleton.elim PUnit.{u+1}
        (inferInstanceAs (Subsingleton PUnit.{u+1}))
        (w : PUnit.{u+1}) (PUnit.unit : PUnit.{u+1})
    simpa only [law, hw] using hs.symm
  | succ n ih =>
    let q : Succ M x → ℝ := fun y => ∑ w : M.Path n y.val, p ⟨y,w⟩
    have hq : Prob q := by
      constructor
      · intro y
        exact Finset.sum_nonneg (fun w _ => hp.1 ⟨y,w⟩)
      · change (∑ y : Succ M x, ∑ w : M.Path n y.val, p ⟨y,w⟩) = 1
        rw [← path_sum_step]
        exact hp.2
    let tail : (y : Succ M x) → M.Path n y.val → ℝ := fun y w =>
      if q y = 0 then M.reference n y.val w else p ⟨y,w⟩ / q y
    have ht (y : Succ M x) : Prob (tail y) := by
      by_cases h : q y = 0
      · simpa only [tail, if_pos h] using M.reference_prob n y.val
      · constructor
        · intro w
          dsimp only [tail]
          rw [if_neg h]
          exact div_nonneg (hp.1 ⟨y,w⟩) (hq.1 y)
        · dsimp only [tail]
          simp only [if_neg h]
          rw [← Finset.sum_div]
          exact div_self h
    have htail (y : Succ M x) (w : M.Path n y.val) : q y * tail y w = p ⟨y,w⟩ := by
      by_cases h : q y = 0
      · have hle : p ⟨y,w⟩ ≤ q y := Finset.single_le_sum (f := fun z : M.Path n y.val => p ⟨y,z⟩)
            (fun z _ => hp.1 ⟨y,z⟩) (Finset.mem_univ w)
        have hp0 : p ⟨y,w⟩ = 0 := le_antisymm (by simpa only [h] using hle) (hp.1 ⟨y,w⟩)
        simp only [h, zero_mul, hp0]
      · dsimp only [tail]
        rw [if_neg h]
        field_simp [h] <;> ring
    have hex : ∀ y : Succ M x, ∃ π : M.Policy n y.val,
        M.law n y.val π = tail y := fun y => ih y.val (tail y) (ht y)
    choose π hπ using hex
    let κ : (y : Succ M x) → M.Policy n y.val := fun y =>
      if q y = 0 then M.referencePolicy n y.val else π y
    have hκ (y : Succ M x) : M.law n y.val (κ y) = tail y := by
      by_cases h : q y = 0
      · simpa only [κ, if_pos h, tail, if_pos h] using M.referencePolicy_law n y.val
      · simpa only [κ, if_neg h] using hπ y
    refine ⟨(⟨q,hq⟩,κ), ?_⟩
    funext w
    change q w.1 * M.law n w.1.val (κ w.1) w.2 = p w
    rw [hκ w.1]
    exact htail w.1 w.2
/-- The original path objective evaluated on an arbitrary feasible path probability. -/
def pathObjective (n : ℕ) (x : X) (p : M.Path n x → ℝ) : ℝ :=
  (∑ w, p w * M.cost n x w) + M.τ * klDivergence p (M.reference n x)

lemma actual_conditional_KL_chain (n : ℕ) (x : X) (π : M.Policy n x) :
    klDivergence (M.law n x π) (M.reference n x) = M.conditionalKL n x π := by
  have split_kl {A : Type u} [Fintype A] {B : A → Type u} [∀ a, Fintype (B a)]
      (q r : A → ℝ) (p s : (a : A) → B a → ℝ)
      (hq : Prob q) (hr : ∀ a, 0 < r a) (hrsum : ∑ a, r a = 1)
      (hp : ∀ a, Prob (p a)) (hs : ∀ a, Prob (s a)) (hspos : ∀ a b, 0 < s a b) :
      klDivergence (fun w : Σ a, B a => q w.1 * p w.1 w.2)
        (fun w : Σ a, B a => r w.1 * s w.1 w.2) = klDivergence q r + ∑ a, q a * klDivergence (p a) (s a) := by
    classical
    let W (w : Σ a, B a) (a : A) : ℝ := if w.1=a then 1 else 0
    let P (w : Σ a, B a) := q w.1*p w.1 w.2
    let Q (w : Σ a, B a) := r w.1*s w.1 w.2
    have out (u : A → ℝ) (v : (a : A) → B a → ℝ) (hv : ∀ a, ∑ b, v a b=1) (a : A) :
        channelOutput W (fun w : Σ a, B a => u w.1*v w.1 w.2) a = u a := by
      unfold channelOutput
      rw [Fintype.sum_sigma]
      calc
        _ = ∑ z, if z=a then u z else 0 := by
          apply Finset.sum_congr rfl
          intro z _
          by_cases h : z=a
          · simp [W,h,← Finset.mul_sum,hv]
          · simp [W,h]
        _ = _ := by simp
    have hP : Prob P := by
      constructor
      · intro w;exact mul_nonneg (hq.1 w.1) ((hp w.1).1 w.2)
      · change (∑ w : Σ a, B a, q w.1*p w.1 w.2)=1
        rw [Fintype.sum_sigma]
        simp_rw [← Finset.mul_sum,fun a => (hp a).2,mul_one]
        exact hq.2
    have hQpos (w : Σ a, B a) : 0 < Q w := mul_pos (hr w.1) (hspos w.1 w.2)
    have hQ : Prob Q := by
      constructor
      · intro w;exact (hQpos w).le
      · change (∑ w : Σ a, B a, r w.1*s w.1 w.2)=1
        rw [Fintype.sum_sigma]
        simp_rw [← Finset.mul_sum,fun a => (hs a).2,mul_one]
        exact hrsum
    have hW : (∀ w a, 0 ≤ W w a) ∧ ∀ w, ∑ a, W w a = 1 := by
      constructor
      · intro w a;dsimp [W];split_ifs <;> norm_num
      · intro w;simp [W]
    have hchain := D5.S3.DivergenceSupport.ZeroSupportDPI.classical_dpi_identity_zero_support
      P Q W hP hQ (fun w hw => ((hQpos w).ne' hw).elim) hW
    have hOp : channelOutput W P = q := funext (out q p (fun a => (hp a).2))
    have hOq : channelOutput W Q = r := funext (out r s (fun a => (hs a).2))
    rw [hOp,hOq] at hchain
    have hf (a : A) : q a * klDivergence (posterior W P a) (posterior W Q a) = q a * klDivergence (p a) (s a) := by
      by_cases hq0 : q a=0
      · simp [hq0]
      congr 1
      unfold klDivergence
      rw [Fintype.sum_sigma]
      calc
        _ = ∑ z, if z=a then ∑ b, p z b*Real.log (p z b/s z b) else 0 := by
          apply Finset.sum_congr rfl
          intro z _
          by_cases hz : z=a
          · subst z
            simp [posterior,W,P,Q,hOp,hOq,hq0,ne_of_gt (hr a)]
          · simp [posterior,W,P,Q,hz]
        _ = _ := by simp
    simpa only [hf] using hchain
  have support_sum (x : X) : ∑ y : Succ M x, M.R x y.val = 1 := by
    classical
    have hs : (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : Succ M x, M.R x y.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    rw [← hs]
    calc
      (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : X, M.R x y := by
        apply Finset.sum_congr rfl
        intro y _
        split_ifs with h
        · rfl
        · exact (le_antisymm (le_of_not_gt h) (M.nonneg x y)).symm
      _ = 1 := M.stochastic x
  have kl_chain_step (n : ℕ) (x : X) (π : M.Policy (n+1) x) :
      klDivergence (M.law (n+1) x π) (M.reference (n+1) x) = klDivergence π.1.q (fun y => M.R x y.val) +
        ∑ y, π.1.q y * klDivergence (M.law n y.val (π.2 y)) (M.reference n y.val) := by
    exact split_kl (A := Succ M x) (B := fun y => M.Path n y.val)
      π.1.q (fun y => M.R x y.val)
      (fun y => M.law n y.val (π.2 y)) (fun y => M.reference n y.val)
      π.1.prob (fun y => y.property) (support_sum x)
      (fun y => M.law_prob n y.val (π.2 y)) (fun y => M.reference_prob n y.val)
      (fun y w => M.reference_pos n y.val w)
  induction n generalizing x with
  | zero => simp [law,reference,conditionalKL,klDivergence]
  | succ n ih => rw [kl_chain_step]; simp only [conditionalKL,ih]
def partition (x : X) (v : X → ℝ) : ℝ := ∑ y : Succ M x, M.R x y.val * Real.exp (-(M.c x y.val + v y.val) / M.τ)
def soft (v : X → ℝ) (x : X) : ℝ := -M.τ * Real.log (M.partition x v)
def star (v : X → ℝ) (x : X) (y : Succ M x) : ℝ :=
  M.R x y.val * Real.exp (-(M.c x y.val + v y.val - M.soft v x) / M.τ)
def value : ℕ → X → ℝ
  | 0 => M.g
  | n+1 => M.soft (value n)
def optimal : (n : ℕ) → (x : X) → M.Policy n x
  | 0, _ => PUnit.unit
  | n+1, x => by
    have support_sum (x : X) : ∑ y : Succ M x, M.R x y.val = 1 := by
      classical
      have hs : (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : Succ M x, M.R x y.val := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype _ (by simp) _
      rw [← hs]
      calc
        (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : X, M.R x y := by
          apply Finset.sum_congr rfl
          intro y _
          split_ifs with h
          · rfl
          · exact (le_antisymm (le_of_not_gt h) (M.nonneg x y)).symm
        _ = 1 := M.stochastic x
    have support_nonempty (x : X) : Nonempty (Succ M x) := by
      classical
      by_contra h
      haveI : IsEmpty (Succ M x) := not_nonempty_iff.mp h
      have := support_sum x
      simp at this
    have partition_pos (x : X) (v : X → ℝ) : 0 < M.partition x v := by
      classical
      letI := support_nonempty x
      exact Finset.sum_pos (fun y _ => mul_pos y.property (Real.exp_pos _)) Finset.univ_nonempty
    have exponential_soft (x : X) (v : X → ℝ) : Real.exp (-M.soft v x / M.τ) = M.partition x v := by
      unfold soft
      have h : -(-M.τ * Real.log (M.partition x v)) / M.τ = Real.log (M.partition x v) := by
        field_simp [ne_of_gt M.temperature]
      rw [h,Real.exp_log (partition_pos x v)]
    have star_div (x : X) (v : X → ℝ) (y : Succ M x) :
        M.star v x y = M.R x y.val * Real.exp (-(M.c x y.val + v y.val)/M.τ) / M.partition x v := by
      have he : -(M.c x y.val + v y.val - M.soft v x)/M.τ =
          -(M.c x y.val + v y.val)/M.τ - (-M.soft v x/M.τ) := by ring
      simp only [star,he,Real.exp_sub,exponential_soft]
      ring
    have star_prob (x : X) (v : X → ℝ) : Prob (M.star v x) := by
      constructor
      · intro y;exact (mul_pos y.property (Real.exp_pos _)).le
      · simp_rw [star_div]
        rw [← Finset.sum_div]
        exact div_self (ne_of_gt (partition_pos x v))
    exact (⟨M.star (M.value n) x,star_prob x (M.value n)⟩,
          fun y => optimal n y.val)
lemma all_history_bound (n : ℕ) (x : X) (π : M.Policy n x) : M.value n x ≤ M.J n x π := by
  have split_kl {A : Type u} [Fintype A] {B : A → Type u} [∀ a, Fintype (B a)]
      (q r : A → ℝ) (p s : (a : A) → B a → ℝ)
      (hq : Prob q) (hr : ∀ a, 0 < r a) (hrsum : ∑ a, r a = 1)
      (hp : ∀ a, Prob (p a)) (hs : ∀ a, Prob (s a)) (hspos : ∀ a b, 0 < s a b) :
      klDivergence (fun w : Σ a, B a => q w.1 * p w.1 w.2)
        (fun w : Σ a, B a => r w.1 * s w.1 w.2) = klDivergence q r + ∑ a, q a * klDivergence (p a) (s a) := by
    classical
    let W (w : Σ a, B a) (a : A) : ℝ := if w.1=a then 1 else 0
    let P (w : Σ a, B a) := q w.1*p w.1 w.2
    let Q (w : Σ a, B a) := r w.1*s w.1 w.2
    have out (u : A → ℝ) (v : (a : A) → B a → ℝ) (hv : ∀ a, ∑ b, v a b=1) (a : A) :
        channelOutput W (fun w : Σ a, B a => u w.1*v w.1 w.2) a = u a := by
      unfold channelOutput
      rw [Fintype.sum_sigma]
      calc
        _ = ∑ z, if z=a then u z else 0 := by
          apply Finset.sum_congr rfl
          intro z _
          by_cases h : z=a
          · simp [W,h,← Finset.mul_sum,hv]
          · simp [W,h]
        _ = _ := by simp
    have hP : Prob P := by
      constructor
      · intro w;exact mul_nonneg (hq.1 w.1) ((hp w.1).1 w.2)
      · change (∑ w : Σ a, B a, q w.1*p w.1 w.2)=1
        rw [Fintype.sum_sigma]
        simp_rw [← Finset.mul_sum,fun a => (hp a).2,mul_one]
        exact hq.2
    have hQpos (w : Σ a, B a) : 0 < Q w := mul_pos (hr w.1) (hspos w.1 w.2)
    have hQ : Prob Q := by
      constructor
      · intro w;exact (hQpos w).le
      · change (∑ w : Σ a, B a, r w.1*s w.1 w.2)=1
        rw [Fintype.sum_sigma]
        simp_rw [← Finset.mul_sum,fun a => (hs a).2,mul_one]
        exact hrsum
    have hW : (∀ w a, 0 ≤ W w a) ∧ ∀ w, ∑ a, W w a = 1 := by
      constructor
      · intro w a;dsimp [W];split_ifs <;> norm_num
      · intro w;simp [W]
    have hchain := D5.S3.DivergenceSupport.ZeroSupportDPI.classical_dpi_identity_zero_support
      P Q W hP hQ (fun w hw => ((hQpos w).ne' hw).elim) hW
    have hOp : channelOutput W P = q := funext (out q p (fun a => (hp a).2))
    have hOq : channelOutput W Q = r := funext (out r s (fun a => (hs a).2))
    rw [hOp,hOq] at hchain
    have hf (a : A) : q a * klDivergence (posterior W P a) (posterior W Q a) = q a * klDivergence (p a) (s a) := by
      by_cases hq0 : q a=0
      · simp [hq0]
      congr 1
      unfold klDivergence
      rw [Fintype.sum_sigma]
      calc
        _ = ∑ z, if z=a then ∑ b, p z b*Real.log (p z b/s z b) else 0 := by
          apply Finset.sum_congr rfl
          intro z _
          by_cases hz : z=a
          · subst z
            simp [posterior,W,P,Q,hOp,hOq,hq0,ne_of_gt (hr a)]
          · simp [posterior,W,P,Q,hz]
        _ = _ := by simp
    simpa only [hf] using hchain
  have support_sum (x : X) : ∑ y : Succ M x, M.R x y.val = 1 := by
    classical
    have hs : (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : Succ M x, M.R x y.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    rw [← hs]
    calc
      (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : X, M.R x y := by
        apply Finset.sum_congr rfl
        intro y _
        split_ifs with h
        · rfl
        · exact (le_antisymm (le_of_not_gt h) (M.nonneg x y)).symm
      _ = 1 := M.stochastic x
  have kl_chain_step (n : ℕ) (x : X) (π : M.Policy (n+1) x) :
      klDivergence (M.law (n+1) x π) (M.reference (n+1) x) = klDivergence π.1.q (fun y => M.R x y.val) +
        ∑ y, π.1.q y * klDivergence (M.law n y.val (π.2 y)) (M.reference n y.val) := by
    exact split_kl (A := Succ M x) (B := fun y => M.Path n y.val)
      π.1.q (fun y => M.R x y.val)
      (fun y => M.law n y.val (π.2 y)) (fun y => M.reference n y.val)
      π.1.prob (fun y => y.property) (support_sum x)
      (fun y => M.law_prob n y.val (π.2 y)) (fun y => M.reference_prob n y.val)
      (fun y w => M.reference_pos n y.val w)
  have path_sum_step (n : ℕ) (x : X) (f : M.Path (n+1) x → ℝ) :
      (∑ w, f w) = ∑ y : Succ M x, ∑ w : M.Path n y.val, f ⟨y,w⟩ := by
    change (∑ w : Σ y : Succ M x, M.Path n y.val, f w) = _
    exact Fintype.sum_sigma _
  have J_step (n : ℕ) (x : X) (π : M.Policy (n+1) x) : M.J (n+1) x π =
        (∑ y, π.1.q y * (M.c x y.val + M.J n y.val (π.2 y))) + M.τ * klDivergence π.1.q (fun y => M.R x y.val) := by
    have hc : (∑ w, M.law (n+1) x π w * M.cost (n+1) x w) =
        ∑ y, π.1.q y * (M.c x y.val + ∑ w, M.law n y.val (π.2 y) w * M.cost n y.val w) := by
      simp only [path_sum_step,law,cost]
      apply Finset.sum_congr rfl
      intro y _
      simp_rw [mul_add,Finset.sum_add_distrib]
      have h1 : (∑ w, π.1.q y * M.law n y.val (π.2 y) w * M.c x y.val) = π.1.q y * M.c x y.val := by
        calc
          _ = π.1.q y * M.c x y.val * ∑ w, M.law n y.val (π.2 y) w := by
            rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro w _;ring
          _ = _ := by rw [(M.law_prob n y.val (π.2 y)).2,mul_one]
      rw [h1]
      simp only [mul_assoc,← Finset.mul_sum,mul_add]
    unfold J
    rw [hc,kl_chain_step]
    simp_rw [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    simp only [mul_assoc,mul_left_comm,mul_comm]
    ring
  have path_sum_zero (x : X) (f : M.Path 0 x → ℝ) : (∑ w, f w) = f PUnit.unit := by
    classical
    refine Finset.sum_eq_single (PUnit.unit : M.Path 0 x) ?_ ?_
    · intro w _ hw
      exact (hw (Subsingleton.elim _ _)).elim
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have row_identity (x : X) (v : X → ℝ) (q : M.Row x) :
      (∑ y, q.q y * (M.c x y.val + v y.val)) + M.τ * klDivergence q.q (fun y => M.R x y.val) =
          M.soft v x + M.τ * klDivergence q.q (M.star v x) := by
    have ht (y : Succ M x) : q.q y * (M.c x y.val + v y.val) +
          M.τ * (q.q y * Real.log (q.q y / M.R x y.val)) =
        q.q y * M.soft v x + M.τ * (q.q y * Real.log (q.q y / M.star v x y)) := by
      by_cases hq : q.q y = 0
      · simp [hq]
      have hr : M.R x y.val ≠ 0 := ne_of_gt y.property
      have hs : M.star v x y ≠ 0 := mul_ne_zero hr (Real.exp_ne_zero _)
      have hl : Real.log (M.star v x y) = Real.log (M.R x y.val) -
          (M.c x y.val + v y.val - M.soft v x) / M.τ := by
        rw [star,Real.log_mul hr (Real.exp_ne_zero _),Real.log_exp];ring
      rw [Real.log_div hq hr,Real.log_div hq hs,hl]
      field_simp [ne_of_gt M.temperature]
      <;> ring
    have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun y _ => ht y)
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,q.prob.2,one_mul] at hsum
    simpa only [klDivergence] using hsum
  have support_nonempty (x : X) : Nonempty (Succ M x) := by
    classical
    by_contra h
    haveI : IsEmpty (Succ M x) := not_nonempty_iff.mp h
    have := support_sum x
    simp at this
  have partition_pos (x : X) (v : X → ℝ) : 0 < M.partition x v := by
    classical
    letI := support_nonempty x
    exact Finset.sum_pos (fun y _ => mul_pos y.property (Real.exp_pos _)) Finset.univ_nonempty
  have exponential_soft (x : X) (v : X → ℝ) : Real.exp (-M.soft v x / M.τ) = M.partition x v := by
    unfold soft
    have h : -(-M.τ * Real.log (M.partition x v)) / M.τ = Real.log (M.partition x v) := by
      field_simp [ne_of_gt M.temperature]
    rw [h,Real.exp_log (partition_pos x v)]
  have star_div (x : X) (v : X → ℝ) (y : Succ M x) :
      M.star v x y = M.R x y.val * Real.exp (-(M.c x y.val + v y.val)/M.τ) / M.partition x v := by
    have he : -(M.c x y.val + v y.val - M.soft v x)/M.τ = -(M.c x y.val + v y.val)/M.τ - (-M.soft v x/M.τ) := by ring
    simp only [star,he,Real.exp_sub,exponential_soft]
    ring
  have star_prob (x : X) (v : X → ℝ) : Prob (M.star v x) := by
    constructor
    · intro y;exact (mul_pos y.property (Real.exp_pos _)).le
    · simp_rw [star_div]
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt (partition_pos x v))
  have row_minimum (x : X) (v : X → ℝ) (q : M.Row x) : M.soft v x ≤ (∑ y, q.q y * (M.c x y.val + v y.val)) +
        M.τ * klDivergence q.q (fun y => M.R x y.val) := by
    rw [row_identity]
    have hk := kl_divergence_nonneg q.q (M.star v x) q.prob (star_prob x v)
      (fun y hy => (mul_ne_zero (ne_of_gt y.property) (Real.exp_ne_zero _) hy).elim)
    exact le_add_of_nonneg_right (mul_nonneg M.temperature.le hk)
  induction n generalizing x with
  | zero => simp [value,J,law,cost,reference,klDivergence,path_sum_zero]
  | succ n ih =>
    rw [J_step]
    calc
      M.value (n+1) x ≤ (∑ y, π.1.q y * (M.c x y.val + M.value n y.val)) +
          M.τ * klDivergence π.1.q (fun y => M.R x y.val) := row_minimum x _ π.1
      _ ≤ _ := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro y _
          have hchild := ih y.val (π.2 y)
          have hc : M.c x y.val+M.value n y.val ≤ M.c x y.val+M.J n y.val (π.2 y) := by linarith
          exact mul_le_mul_of_nonneg_left hc (π.1.prob.1 y)
        · exact le_rfl
lemma optimal_attains (n : ℕ) (x : X) : M.J n x (M.optimal n x) = M.value n x := by
  have split_kl {A : Type u} [Fintype A] {B : A → Type u} [∀ a, Fintype (B a)]
      (q r : A → ℝ) (p s : (a : A) → B a → ℝ)
      (hq : Prob q) (hr : ∀ a, 0 < r a) (hrsum : ∑ a, r a = 1)
      (hp : ∀ a, Prob (p a)) (hs : ∀ a, Prob (s a)) (hspos : ∀ a b, 0 < s a b) :
      klDivergence (fun w : Σ a, B a => q w.1 * p w.1 w.2)
        (fun w : Σ a, B a => r w.1 * s w.1 w.2) = klDivergence q r + ∑ a, q a * klDivergence (p a) (s a) := by
    classical
    let W (w : Σ a, B a) (a : A) : ℝ := if w.1=a then 1 else 0
    let P (w : Σ a, B a) := q w.1*p w.1 w.2
    let Q (w : Σ a, B a) := r w.1*s w.1 w.2
    have out (u : A → ℝ) (v : (a : A) → B a → ℝ) (hv : ∀ a, ∑ b, v a b=1) (a : A) :
        channelOutput W (fun w : Σ a, B a => u w.1*v w.1 w.2) a = u a := by
      unfold channelOutput
      rw [Fintype.sum_sigma]
      calc
        _ = ∑ z, if z=a then u z else 0 := by
          apply Finset.sum_congr rfl
          intro z _
          by_cases h : z=a
          · simp [W,h,← Finset.mul_sum,hv]
          · simp [W,h]
        _ = _ := by simp
    have hP : Prob P := by
      constructor
      · intro w;exact mul_nonneg (hq.1 w.1) ((hp w.1).1 w.2)
      · change (∑ w : Σ a, B a, q w.1*p w.1 w.2)=1
        rw [Fintype.sum_sigma]
        simp_rw [← Finset.mul_sum,fun a => (hp a).2,mul_one]
        exact hq.2
    have hQpos (w : Σ a, B a) : 0 < Q w := mul_pos (hr w.1) (hspos w.1 w.2)
    have hQ : Prob Q := by
      constructor
      · intro w;exact (hQpos w).le
      · change (∑ w : Σ a, B a, r w.1*s w.1 w.2)=1
        rw [Fintype.sum_sigma]
        simp_rw [← Finset.mul_sum,fun a => (hs a).2,mul_one]
        exact hrsum
    have hW : (∀ w a, 0 ≤ W w a) ∧ ∀ w, ∑ a, W w a = 1 := by
      constructor
      · intro w a;dsimp [W];split_ifs <;> norm_num
      · intro w;simp [W]
    have hchain := D5.S3.DivergenceSupport.ZeroSupportDPI.classical_dpi_identity_zero_support
      P Q W hP hQ (fun w hw => ((hQpos w).ne' hw).elim) hW
    have hOp : channelOutput W P = q := funext (out q p (fun a => (hp a).2))
    have hOq : channelOutput W Q = r := funext (out r s (fun a => (hs a).2))
    rw [hOp,hOq] at hchain
    have hf (a : A) : q a * klDivergence (posterior W P a) (posterior W Q a) = q a * klDivergence (p a) (s a) := by
      by_cases hq0 : q a=0
      · simp [hq0]
      congr 1
      unfold klDivergence
      rw [Fintype.sum_sigma]
      calc
        _ = ∑ z, if z=a then ∑ b, p z b*Real.log (p z b/s z b) else 0 := by
          apply Finset.sum_congr rfl
          intro z _
          by_cases hz : z=a
          · subst z
            simp [posterior,W,P,Q,hOp,hOq,hq0,ne_of_gt (hr a)]
          · simp [posterior,W,P,Q,hz]
        _ = _ := by simp
    simpa only [hf] using hchain
  have support_sum (x : X) : ∑ y : Succ M x, M.R x y.val = 1 := by
    classical
    have hs : (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : Succ M x, M.R x y.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    rw [← hs]
    calc
      (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : X, M.R x y := by
        apply Finset.sum_congr rfl
        intro y _
        split_ifs with h
        · rfl
        · exact (le_antisymm (le_of_not_gt h) (M.nonneg x y)).symm
      _ = 1 := M.stochastic x
  have kl_chain_step (n : ℕ) (x : X) (π : M.Policy (n+1) x) :
      klDivergence (M.law (n+1) x π) (M.reference (n+1) x) = klDivergence π.1.q (fun y => M.R x y.val) +
        ∑ y, π.1.q y * klDivergence (M.law n y.val (π.2 y)) (M.reference n y.val) := by
    exact split_kl (A := Succ M x) (B := fun y => M.Path n y.val)
      π.1.q (fun y => M.R x y.val)
      (fun y => M.law n y.val (π.2 y)) (fun y => M.reference n y.val)
      π.1.prob (fun y => y.property) (support_sum x)
      (fun y => M.law_prob n y.val (π.2 y)) (fun y => M.reference_prob n y.val)
      (fun y w => M.reference_pos n y.val w)
  have path_sum_step (n : ℕ) (x : X) (f : M.Path (n+1) x → ℝ) :
      (∑ w, f w) = ∑ y : Succ M x, ∑ w : M.Path n y.val, f ⟨y,w⟩ := by
    change (∑ w : Σ y : Succ M x, M.Path n y.val, f w) = _
    exact Fintype.sum_sigma _
  have J_step (n : ℕ) (x : X) (π : M.Policy (n+1) x) : M.J (n+1) x π =
        (∑ y, π.1.q y * (M.c x y.val + M.J n y.val (π.2 y))) + M.τ * klDivergence π.1.q (fun y => M.R x y.val) := by
    have hc : (∑ w, M.law (n+1) x π w * M.cost (n+1) x w) =
        ∑ y, π.1.q y * (M.c x y.val + ∑ w, M.law n y.val (π.2 y) w * M.cost n y.val w) := by
      simp only [path_sum_step,law,cost]
      apply Finset.sum_congr rfl
      intro y _
      simp_rw [mul_add,Finset.sum_add_distrib]
      have h1 : (∑ w, π.1.q y * M.law n y.val (π.2 y) w * M.c x y.val) = π.1.q y * M.c x y.val := by
        calc
          _ = π.1.q y * M.c x y.val * ∑ w, M.law n y.val (π.2 y) w := by
            rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro w _;ring
          _ = _ := by rw [(M.law_prob n y.val (π.2 y)).2,mul_one]
      rw [h1]
      simp only [mul_assoc,← Finset.mul_sum,mul_add]
    unfold J
    rw [hc,kl_chain_step]
    simp_rw [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    simp only [mul_assoc,mul_left_comm,mul_comm]
    ring
  have path_sum_zero (x : X) (f : M.Path 0 x → ℝ) : (∑ w, f w) = f PUnit.unit := by
    classical
    refine Finset.sum_eq_single (PUnit.unit : M.Path 0 x) ?_ ?_
    · intro w _ hw
      exact (hw (Subsingleton.elim _ _)).elim
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have row_identity (x : X) (v : X → ℝ) (q : M.Row x) :
      (∑ y, q.q y * (M.c x y.val + v y.val)) + M.τ * klDivergence q.q (fun y => M.R x y.val) =
          M.soft v x + M.τ * klDivergence q.q (M.star v x) := by
    have ht (y : Succ M x) : q.q y * (M.c x y.val + v y.val) +
          M.τ * (q.q y * Real.log (q.q y / M.R x y.val)) =
        q.q y * M.soft v x + M.τ * (q.q y * Real.log (q.q y / M.star v x y)) := by
      by_cases hq : q.q y = 0
      · simp [hq]
      have hr : M.R x y.val ≠ 0 := ne_of_gt y.property
      have hs : M.star v x y ≠ 0 := mul_ne_zero hr (Real.exp_ne_zero _)
      have hl : Real.log (M.star v x y) = Real.log (M.R x y.val) -
          (M.c x y.val + v y.val - M.soft v x) / M.τ := by
        rw [star,Real.log_mul hr (Real.exp_ne_zero _),Real.log_exp];ring
      rw [Real.log_div hq hr,Real.log_div hq hs,hl]
      field_simp [ne_of_gt M.temperature]
      <;> ring
    have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun y _ => ht y)
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,q.prob.2,one_mul] at hsum
    simpa only [klDivergence] using hsum
  have support_nonempty (x : X) : Nonempty (Succ M x) := by
    classical
    by_contra h
    haveI : IsEmpty (Succ M x) := not_nonempty_iff.mp h
    have := support_sum x
    simp at this
  have partition_pos (x : X) (v : X → ℝ) : 0 < M.partition x v := by
    classical
    letI := support_nonempty x
    exact Finset.sum_pos (fun y _ => mul_pos y.property (Real.exp_pos _)) Finset.univ_nonempty
  have exponential_soft (x : X) (v : X → ℝ) : Real.exp (-M.soft v x / M.τ) = M.partition x v := by
    unfold soft
    have h : -(-M.τ * Real.log (M.partition x v)) / M.τ = Real.log (M.partition x v) := by
      field_simp [ne_of_gt M.temperature]
    rw [h,Real.exp_log (partition_pos x v)]
  have star_div (x : X) (v : X → ℝ) (y : Succ M x) :
      M.star v x y = M.R x y.val * Real.exp (-(M.c x y.val + v y.val)/M.τ) / M.partition x v := by
    have he : -(M.c x y.val + v y.val - M.soft v x)/M.τ = -(M.c x y.val + v y.val)/M.τ - (-M.soft v x/M.τ) := by ring
    simp only [star,he,Real.exp_sub,exponential_soft]
    ring
  have star_prob (x : X) (v : X → ℝ) : Prob (M.star v x) := by
    constructor
    · intro y;exact (mul_pos y.property (Real.exp_pos _)).le
    · simp_rw [star_div]
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt (partition_pos x v))
  induction n generalizing x with
  | zero => simp [J,law,cost,reference,value,klDivergence,path_sum_zero]
  | succ n ih =>
    rw [J_step]
    simp only [optimal,ih]
    have hr := row_identity x (M.value n)
      (⟨M.star (M.value n) x,star_prob x (M.value n)⟩ : M.Row x)
    simpa [klDivergence,value] using hr
def hardRow (v : X → ℝ) (x : X) : ℝ := by
  have support_sum (x : X) : ∑ y : Succ M x, M.R x y.val = 1 := by
    classical
    have hs : (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : Succ M x, M.R x y.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    rw [← hs]
    calc
      (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : X, M.R x y := by
        apply Finset.sum_congr rfl
        intro y _
        split_ifs with h
        · rfl
        · exact (le_antisymm (le_of_not_gt h) (M.nonneg x y)).symm
      _ = 1 := M.stochastic x
  have support_nonempty (x : X) : Nonempty (Succ M x) := by
    classical
    by_contra h
    haveI : IsEmpty (Succ M x) := not_nonempty_iff.mp h
    have := support_sum x
    simp at this
  classical
  letI := support_nonempty x
  exact (Finset.univ.image (fun y : Succ M x => M.c x y.val+v y.val)).min'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)
abbrev PosEdge := {p : X × X // 0 < M.R p.1 p.2}
instance : Fintype M.PosEdge := Fintype.ofFinite _
def rmin (x0 : X) : ℝ := by
  have support_sum (x : X) : ∑ y : Succ M x, M.R x y.val = 1 := by
    classical
    have hs : (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : Succ M x, M.R x y.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    rw [← hs]
    calc
      (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : X, M.R x y := by
        apply Finset.sum_congr rfl
        intro y _
        split_ifs with h
        · rfl
        · exact (le_antisymm (le_of_not_gt h) (M.nonneg x y)).symm
      _ = 1 := M.stochastic x
  have support_nonempty (x : X) : Nonempty (Succ M x) := by
    classical
    by_contra h
    haveI : IsEmpty (Succ M x) := not_nonempty_iff.mp h
    have := support_sum x
    simp at this
  classical
  let y : Succ M x0 := Classical.choice (support_nonempty x0)
  letI : Nonempty M.PosEdge := ⟨⟨(x0,y.val),y.property⟩⟩
  exact (Finset.univ.image (fun e : M.PosEdge => M.R e.val.1 e.val.2)).min'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)
lemma soft_hard_row (v : X → ℝ) (x x0 : X) : M.hardRow v x ≤ M.soft v x ∧
      M.soft v x ≤ M.hardRow v x + M.τ * Real.log (1/M.rmin x0) := by
  have support_sum (x : X) : ∑ y : Succ M x, M.R x y.val = 1 := by
    classical
    have hs : (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : Succ M x, M.R x y.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    rw [← hs]
    calc
      (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : X, M.R x y := by
        apply Finset.sum_congr rfl
        intro y _
        split_ifs with h
        · rfl
        · exact (le_antisymm (le_of_not_gt h) (M.nonneg x y)).symm
      _ = 1 := M.stochastic x
  have support_nonempty (x : X) : Nonempty (Succ M x) := by
    classical
    by_contra h
    haveI : IsEmpty (Succ M x) := not_nonempty_iff.mp h
    have := support_sum x
    simp at this
  have hardRow_attained (v : X → ℝ) (x : X) : ∃ y : Succ M x, M.hardRow v x = M.c x y.val+v y.val := by
    classical
    obtain ⟨y,_,hy⟩ := Finset.mem_image.mp (Finset.min'_mem
      (Finset.univ.image (fun y : Succ M x => M.c x y.val+v y.val))
      (by letI := support_nonempty x;exact Finset.image_nonempty.mpr Finset.univ_nonempty))
    exact ⟨y,hy.symm⟩
  have hardRow_le (v : X → ℝ) (x : X) (y : Succ M x) : M.hardRow v x ≤ M.c x y.val+v y.val := by
    classical
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨y,Finset.mem_univ y,rfl⟩)
  have partition_pos (x : X) (v : X → ℝ) : 0 < M.partition x v := by
    classical
    letI := support_nonempty x
    exact Finset.sum_pos (fun y _ => mul_pos y.property (Real.exp_pos _)) Finset.univ_nonempty
  have rmin_facts (x0 : X) : 0 < M.rmin x0 ∧ M.rmin x0 ≤ 1 ∧
      ∀ x y, 0 < M.R x y → M.rmin x0 ≤ M.R x y := by
    classical
    have he : ∃ e : M.PosEdge, M.rmin x0 = M.R e.val.1 e.val.2 := by
      obtain ⟨e,_,he⟩ := Finset.mem_image.mp (Finset.min'_mem
        (Finset.univ.image (fun e : M.PosEdge => M.R e.val.1 e.val.2))
        (by obtain ⟨y⟩ := support_nonempty x0
            letI : Nonempty M.PosEdge := ⟨⟨(x0,y.val),y.property⟩⟩
            exact Finset.image_nonempty.mpr Finset.univ_nonempty))
      exact ⟨e,he.symm⟩
    obtain ⟨e,he⟩ := he
    refine ⟨by rw [he];exact e.property,?_,?_⟩
    · rw [he]
      exact (Finset.single_le_sum (fun y _ => M.nonneg e.val.1 y) (Finset.mem_univ e.val.2)).trans
        (le_of_eq (M.stochastic e.val.1))
    · intro x y h
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨(⟨(x,y),h⟩ : M.PosEdge),Finset.mem_univ _,rfl⟩)
  have hτ := M.temperature
  have hr := rmin_facts x0
  have hz := partition_pos x v
  have hu : M.partition x v ≤ Real.exp (-M.hardRow v x/M.τ) := by
    calc
      _ ≤ ∑ y : Succ M x, M.R x y.val * Real.exp (-M.hardRow v x/M.τ) := by
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_mul_of_nonneg_left _ y.property.le
        apply Real.exp_le_exp.mpr
        exact div_le_div_of_nonneg_right (by linarith [hardRow_le v x y]) hτ.le
      _ = _ := by rw [← Finset.sum_mul,support_sum,one_mul]
  obtain ⟨y,hy⟩ := hardRow_attained v x
  have hl : M.rmin x0 * Real.exp (-M.hardRow v x/M.τ) ≤ M.partition x v := by
    calc
      _ ≤ M.R x y.val * Real.exp (-M.hardRow v x/M.τ) :=
        mul_le_mul_of_nonneg_right (hr.2.2 x y.val y.property) (Real.exp_pos _).le
      _ = M.R x y.val * Real.exp (-(M.c x y.val+v y.val)/M.τ) := by rw [hy]
      _ ≤ _ := by
        change M.R x y.val * Real.exp (-(M.c x y.val + v y.val) / M.τ) ≤
          ∑ z : Succ M x, M.R x z.val * Real.exp (-(M.c x z.val + v z.val) / M.τ)
        exact Finset.single_le_sum
          (f := fun z : Succ M x =>
            M.R x z.val * Real.exp (-(M.c x z.val + v z.val) / M.τ))
          (fun (z : Succ M x) _ => mul_nonneg z.property.le (Real.exp_pos _).le)
          (Finset.mem_univ y)
  have hlogu := Real.log_le_log hz hu
  have hlogl := Real.log_le_log (mul_pos hr.1 (Real.exp_pos _)) hl
  rw [Real.log_exp] at hlogu
  rw [Real.log_mul (ne_of_gt hr.1) (Real.exp_ne_zero _),Real.log_exp] at hlogl
  have hi : Real.log (1/M.rmin x0) = -Real.log (M.rmin x0) := by
    rw [Real.log_div one_ne_zero (ne_of_gt hr.1),Real.log_one];ring
  unfold soft
  rw [hi]
  constructor
  · have := (mul_le_mul_of_nonneg_left hlogu hτ.le)
    field_simp [ne_of_gt hτ] at this
    nlinarith
  · have := (mul_le_mul_of_nonneg_left hlogl hτ.le)
    field_simp [ne_of_gt hτ] at this
    nlinarith
def hard : ℕ → X → ℝ
  | 0 => M.g
  | n+1 => M.hardRow (hard n)
lemma accumulated_hard_min_error (n : ℕ) (x0 : X) : ∀ x, 0 ≤ M.value n x-M.hard n x ∧
      M.value n x-M.hard n x ≤ (n : ℝ)*M.τ*Real.log (1/M.rmin x0) := by
  have support_sum (x : X) : ∑ y : Succ M x, M.R x y.val = 1 := by
    classical
    have hs : (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : Succ M x, M.R x y.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    rw [← hs]
    calc
      (∑ y : X, if 0 < M.R x y then M.R x y else 0) = ∑ y : X, M.R x y := by
        apply Finset.sum_congr rfl
        intro y _
        split_ifs with h
        · rfl
        · exact (le_antisymm (le_of_not_gt h) (M.nonneg x y)).symm
      _ = 1 := M.stochastic x
  have support_nonempty (x : X) : Nonempty (Succ M x) := by
    classical
    by_contra h
    haveI : IsEmpty (Succ M x) := not_nonempty_iff.mp h
    have := support_sum x
    simp at this
  have partition_pos (x : X) (v : X → ℝ) : 0 < M.partition x v := by
    classical
    letI := support_nonempty x
    exact Finset.sum_pos (fun y _ => mul_pos y.property (Real.exp_pos _)) Finset.univ_nonempty
  have soft_monotone (v w : X → ℝ) (h : ∀ y, v y ≤ w y) (x : X) : M.soft v x ≤ M.soft w x := by
    have hz : M.partition x w ≤ M.partition x v := by
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ y.property.le
      apply Real.exp_le_exp.mpr
      exact div_le_div_of_nonneg_right (by linarith [h y.val]) M.temperature.le
    have hl := Real.log_le_log (partition_pos x w) hz
    unfold soft
    nlinarith [M.temperature]
  have soft_shift (v : X → ℝ) (a : ℝ) (x : X) : M.soft (fun y => v y+a) x = M.soft v x+a := by
    have hz : M.partition x (fun y => v y+a) = M.partition x v * Real.exp (-a/M.τ) := by
      unfold partition
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      have he : -(M.c x y.val+(v y.val+a))/M.τ = -(M.c x y.val+v y.val)/M.τ + -a/M.τ := by ring
      rw [he,Real.exp_add];ring
    unfold soft
    rw [hz,Real.log_mul (ne_of_gt (partition_pos x v)) (Real.exp_ne_zero _),Real.log_exp]
    field_simp [ne_of_gt M.temperature]
    <;> ring
  induction n with
  | zero => intro x;simp [value,hard]
  | succ n ih =>
    intro x
    let ε := M.τ*Real.log (1/M.rmin x0)
    have hm := soft_monotone (M.hard n) (M.value n)
      (fun y => by have := (ih y).1;linarith) x
    have hu := soft_monotone (M.value n) (fun y => M.hard n y+(n:ℝ)*ε)
      (fun y => by have := (ih y).2;dsimp [ε];nlinarith) x
    rw [soft_shift] at hu
    have hb := M.soft_hard_row (M.hard n) x x0
    simp only [value,hard]
    constructor
    · linarith [hb.1]
    · push_cast
      dsimp [ε] at hu
      nlinarith [hb.2]
/-- The original backward time convention, with H=0 included. -/
def V (H t : ℕ) : X → ℝ := M.value (H-t)
def D (H t : ℕ) : X → ℝ := M.hard (H-t)
#check @accumulated_hard_min_error
#print axioms accumulated_hard_min_error
#check @actual_conditional_KL_chain
#print axioms actual_conditional_KL_chain
#check @all_history_bound
#print axioms all_history_bound
#check @law_factorization
#print axioms law_factorization
#check @law_prob
#print axioms law_prob
#check @optimal_attains
#print axioms optimal_attains
#check @path_nonempty
#print axioms path_nonempty
#check @referencePolicy_law
#print axioms referencePolicy_law
#check @reference_pos
#print axioms reference_pos
#check @reference_prob
#print axioms reference_prob
#check @soft_hard_row
#print axioms soft_hard_row
end Model
end FiniteHistorySoftControl
