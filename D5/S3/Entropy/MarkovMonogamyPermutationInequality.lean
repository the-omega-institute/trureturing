/- GID: D5/S3/Entropy/MarkovMonogamyPermutationInequality
   generality: G
   mirror-B: D5/B/S3/Entropy/MarkovMonogamyPermutationInequality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every finite Markov chain satisfies the permutation monogamy inequality. -/

import D5.S3.Entropy.Mixing.MixtureEntropyBracket
import D5.S3.Entropy.Submodularity.ConditionalMutualInformation
import Mathlib.GroupTheory.Perm.Fin

/-! Finite Markov laws, their four-point information rectangles, and permutation exchange. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Entropy.MarkovMonogamyPermutationInequality

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.MutualInformationEntropy
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.Mixing.MixtureEntropyBracket
open D5.S3.Entropy.Submodularity.ConditionalMutualInformation
open D5.S3.Entropy.Submodularity.StrongSubadditivity

/-- The matrix product of the successive transitions from position `s` to position `t`.
Only transitions with indices in the half-open interval `[s,t)` are read. -/
noncomputable def composedTransition {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (k : ∀ t, α t → α (t + 1) → ℝ) (s t : ℕ) (h : s ≤ t) : α s → α t → ℝ := by
  classical
  exact Nat.leRecOn (C := fun t => α s → α t → ℝ) h
    (fun {t} u a b => ∑ c, u a c * k t c b) (fun a b => if a = b then 1 else 0)

/-- The initial law pushed through the transitions preceding position `t`. -/
noncomputable def positionLaw {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (p : α 0 → ℝ) (k : ∀ t, α t → α (t + 1) → ℝ) (t : ℕ) (b : α t) : ℝ :=
  ∑ a, p a * composedTransition k 0 t (Nat.zero_le t) a b

/-- The joint mass at two ordered positions: the earlier law times the intervening channel. -/
noncomputable def pairLaw {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (p : α 0 → ℝ) (k : ∀ t, α t → α (t + 1) → ℝ)
    (s t : ℕ) (h : s ≤ t) (q : α s × α t) : ℝ :=
  positionLaw p k s q.1 * composedTransition k s t h q.1 q.2

/-- Positions are `Xₙ,…,X₁,Y₁,…,Yₙ`. The alphabet family outside the first `2*n`
positions is irrelevant; stochasticity is required only for transitions inside this chain.
For `n = 0` both sums are empty. -/
def claim : Prop :=
  ∀ (n : ℕ) (α : ℕ → Type) [∀ t, Fintype (α t)]
    (p : α 0 → ℝ) (k : ∀ t, α t → α (t + 1) → ℝ),
    ((∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1) →
    (∀ t, t + 1 < 2 * n → (∀ a b, 0 ≤ k t a b) ∧ ∀ a, ∑ b, k t a b = 1) →
    ∀ f : Equiv.Perm (Fin n),
      (∑ i : Fin n, mutualInformation
        (pairLaw p k (n - 1 - i.val) (n + (f i).val) (by omega))) ≤
      ∑ i : Fin n, mutualInformation
        (pairLaw p k (n - 1 - i.val) (n + i.val) (by omega))

private theorem composed_self {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (k : ∀ t, α t → α (t + 1) → ℝ) (s : ℕ) (a b : α s) :
    composedTransition k s s (le_refl s) a b =
      @ite ℝ (a = b) (Classical.propDecidable _) 1 0 := by
  classical
  unfold composedTransition
  rw [Nat.leRecOn_self]

private theorem composed_step {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (k : ∀ t, α t → α (t + 1) → ℝ) (s t : ℕ) (h : s ≤ t)
    (a : α s) (b : α (t + 1)) :
    composedTransition k s (t + 1) (by omega) a b =
      ∑ c, composedTransition k s t h a c * k t c b := by
  classical
  unfold composedTransition
  rw [Nat.leRecOn_succ h]

private theorem composed_comp {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (k : ∀ t, α t → α (t + 1) → ℝ) (s u t : ℕ) (hsu : s ≤ u) (hut : u ≤ t)
    (a : α s) (b : α t) :
    composedTransition k s t (hsu.trans hut) a b =
      ∑ c, composedTransition k s u hsu a c * composedTransition k u t hut c b := by
  classical
  induction t, hut using Nat.le_induction with
  | base =>
    simp only [composed_self, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  | succ t hut ih =>
    rw [composed_step k s t (hsu.trans hut)]
    simp_rw [ih, composed_step k u t hut, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    ring

private theorem composed_stochastic {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (k : ∀ t, α t → α (t + 1) → ℝ) (s t : ℕ) (h : s ≤ t)
    (hk : ∀ u, s ≤ u → u < t →
      (∀ a b, 0 ≤ k u a b) ∧ ∀ a, ∑ b, k u a b = 1) :
    (∀ a b, 0 ≤ composedTransition k s t h a b) ∧
      ∀ a, ∑ b, composedTransition k s t h a b = 1 := by
  classical
  induction t, h using Nat.le_induction with
  | base =>
    constructor
    · intro a b
      rw [composed_self]
      split_ifs <;> norm_num
    · intro a
      simp only [composed_self, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  | succ t h ih =>
    have ht := hk t h (Nat.lt_succ_self t)
    have hi := ih (fun u hsu hut => hk u hsu (Nat.lt_succ_of_lt hut))
    constructor
    · intro a b
      rw [composed_step k s t h]
      exact Finset.sum_nonneg fun c _ => mul_nonneg (hi.1 a c) (ht.1 c b)
    · intro a
      simp_rw [composed_step k s t h]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, ht.2, mul_one]
      exact hi.2 a

private theorem position_transport {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (p : α 0 → ℝ) (k : ∀ t, α t → α (t + 1) → ℝ)
    (s t : ℕ) (h : s ≤ t) (b : α t) :
    positionLaw p k t b = ∑ a, positionLaw p k s a * composedTransition k s t h a b := by
  classical
  unfold positionLaw
  simp_rw [composed_comp k 0 s t (Nat.zero_le s) h, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  ring

private theorem position_is_law {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (p : α 0 → ℝ) (k : ∀ t, α t → α (t + 1) → ℝ) (t : ℕ)
    (hp : (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1)
    (hk : ∀ u, u < t → (∀ a b, 0 ≤ k u a b) ∧ ∀ a, ∑ b, k u a b = 1) :
    (∀ a, 0 ≤ positionLaw p k t a) ∧ ∑ a, positionLaw p k t a = 1 := by
  classical
  have ht := composed_stochastic k 0 t (Nat.zero_le t) (fun u _ hu => hk u hu)
  constructor
  · intro a
    unfold positionLaw
    exact Finset.sum_nonneg fun b _ => mul_nonneg (hp.1 b) (ht.1 b a)
  · unfold positionLaw
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ht.2, mul_one]
    exact hp.2

private theorem entropy_channel {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (u : α → β → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hu : ∀ a b, 0 ≤ u a b) (hrow : ∀ a, ∑ b, u a b = 1) :
    shannonEntropy (mixtureJoint p u) =
      shannonEntropy p + ∑ a, p a * shannonEntropy (u a) := by
  rw [entropy_chain_rule (mixtureJoint p u) (fun q => mul_nonneg (hp q.1) (hu q.1 q.2)),
    mixtureJoint_marginal_eq_weight p u hrow,
    mixtureJoint_conditionalEntropy_eq_weighted p u hrow]

set_option maxHeartbeats 800000 in
private theorem four_point_rectangle {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (p : α → ℝ) (u : α → β → ℝ) (v : β → γ → ℝ) (w : γ → δ → ℝ)
    (hp : (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1)
    (hu : (∀ a b, 0 ≤ u a b) ∧ ∀ a, ∑ b, u a b = 1)
    (hv : (∀ b c, 0 ≤ v b c) ∧ ∀ b, ∑ c, v b c = 1)
    (hw : (∀ c d, 0 ≤ w c d) ∧ ∀ c, ∑ d, w c d = 1) :
    mutualInformation (fun q : β × γ => (∑ a, p a * u a q.1) * v q.1 q.2) +
      mutualInformation (fun q : α × δ => p q.1 * ∑ b, u q.1 b * ∑ c, v b c * w c q.2) ≥
    mutualInformation (fun q : β × δ => (∑ a, p a * u a q.1) * ∑ c, v q.1 c * w c q.2) +
      mutualInformation (fun q : α × γ => p q.1 * ∑ b, u q.1 b * v b q.2) := by
  classical
  let r : β → ℝ := fun b => ∑ a, p a * u a b
  let s : α → γ → ℝ := fun a c => ∑ b, u a b * v b c
  let t : β → δ → ℝ := fun b d => ∑ c, v b c * w c d
  let z : α → δ → ℝ := fun a d => ∑ b, u a b * t b d
  let ab := mixtureJoint p u
  let bc := mixtureJoint r v
  let ac := mixtureJoint p s
  let bd := mixtureJoint r t
  let ad := mixtureJoint p z
  let abc := mixtureJoint ab (fun q c => v q.2 c)
  let abd := mixtureJoint ab (fun q d => t q.2 d)
  let acd := mixtureJoint ac (fun q d => w q.2 d)
  let abcd := mixtureJoint abc (fun q d => w q.2 d)
  let e : ((α × δ) × (β × γ)) ≃ (((α × β) × γ) × δ) :=
    { toFun := fun q => (((q.1.1, q.2.1), q.2.2), q.1.2)
      invFun := fun q => ((q.1.1.1, q.2), (q.1.1.2, q.1.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let q : (α × δ) × (β × γ) → ℝ := fun x => abcd (e x)
  have hr0 (b) : 0 ≤ r b := Finset.sum_nonneg fun a _ => mul_nonneg (hp.1 a) (hu.1 a b)
  have hs0 (a c) : 0 ≤ s a c := Finset.sum_nonneg fun b _ => mul_nonneg (hu.1 a b) (hv.1 b c)
  have ht0 (b d) : 0 ≤ t b d := Finset.sum_nonneg fun c _ => mul_nonneg (hv.1 b c) (hw.1 c d)
  have hz0 (a d) : 0 ≤ z a d := Finset.sum_nonneg fun b _ => mul_nonneg (hu.1 a b) (ht0 b d)
  have hs1 (a) : ∑ c, s a c = 1 := by
    dsimp only [s]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hv.2, mul_one]
    exact hu.2 a
  have ht1 (b) : ∑ d, t b d = 1 := by
    dsimp only [t]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hw.2, mul_one]
    exact hv.2 b
  have hz1 (a) : ∑ d, z a d = 1 := by
    dsimp only [z]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ht1, mul_one]
    exact hu.2 a
  have hab0 (x) : 0 ≤ ab x := mul_nonneg (hp.1 x.1) (hu.1 x.1 x.2)
  have hbc0 (x) : 0 ≤ bc x := mul_nonneg (hr0 x.1) (hv.1 x.1 x.2)
  have hac0 (x) : 0 ≤ ac x := mul_nonneg (hp.1 x.1) (hs0 x.1 x.2)
  have hbd0 (x) : 0 ≤ bd x := mul_nonneg (hr0 x.1) (ht0 x.1 x.2)
  have had0 (x) : 0 ≤ ad x := mul_nonneg (hp.1 x.1) (hz0 x.1 x.2)
  have habc0 (x) : 0 ≤ abc x := mul_nonneg (hab0 x.1) (hv.1 x.1.2 x.2)
  have habcd0 (x) : 0 ≤ abcd x := mul_nonneg (habc0 x.1) (hw.1 x.1.2 x.2)
  have hq0 (x) : 0 ≤ q x := habcd0 (e x)
  have habcd1 : ∑ x, abcd x = 1 := by
    dsimp only [abcd, abc, ab, mixtureJoint]
    simp only [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hw.2, mul_one, hv.2, hu.2]
    exact hp.2
  have hq1 : ∑ x, q x = 1 :=
    (Fintype.sum_equiv e _ _ (fun _ => rfl)).trans habcd1
  have hxy : xyProjection q = fun x => abd ((x.1.1, x.2), x.1.2) := by
    funext x
    unfold xyProjection
    dsimp only [q, e, abcd, abc, ab, abd, mixtureJoint, t]
    simp only [Equiv.coe_fn_mk, Finset.mul_sum, mul_assoc]
  have hxz : xzProjection q = fun x => acd ((x.1.1, x.2), x.1.2) := by
    funext x
    unfold xzProjection
    dsimp only [q, e, abcd, abc, ab, acd, ac, mixtureJoint, s]
    simp only [Equiv.coe_fn_mk, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  have had : marginal q = ad := by
    funext x
    unfold marginal
    dsimp only [q, e, abcd, abc, ab, ad, z, t, mixtureJoint]
    simp only [Equiv.coe_fn_mk, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
  have hxyh : shannonEntropy (xyProjection q) = shannonEntropy abd := by
    rw [hxy]
    exact Fintype.sum_equiv
      { toFun := fun x : (α × δ) × β => ((x.1.1, x.2), x.1.2)
        invFun := fun x => ((x.1.1, x.2), x.1.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl } _ _ (fun _ => rfl)
  have hxzh : shannonEntropy (xzProjection q) = shannonEntropy acd := by
    rw [hxz]
    exact Fintype.sum_equiv
      { toFun := fun x : (α × δ) × γ => ((x.1.1, x.2), x.1.2)
        invFun := fun x => ((x.1.1, x.2), x.1.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl } _ _ (fun _ => rfl)
  have hqh : shannonEntropy q = shannonEntropy abcd :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  have weight (f : β → ℝ) : (∑ x, ab x * f x.2) = ∑ b, r b * f b := by
    dsimp only [ab, mixtureJoint, r]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Finset.sum_mul]
  have weightw : (∑ x, ac x * shannonEntropy (w x.2)) =
      ∑ x, abc x * shannonEntropy (w x.2) := by
    dsimp only [ac, abc, ab, s, mixtureJoint]
    simp only [Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  have hcond := conditional_mutual_information_nonneg q ⟨hq0, hq1⟩
  rw [conditional_mutual_information_eq_entropy_defect q hq0,
    hxyh, hxzh, hqh, had] at hcond
  have habdh := entropy_channel ab (fun x d => t x.2 d) hab0
    (fun x d => ht0 x.2 d) (fun x => ht1 x.2)
  have hacdh := entropy_channel ac (fun x d => w x.2 d) hac0
    (fun x d => hw.1 x.2 d) (fun x => hw.2 x.2)
  have habcdh := entropy_channel abc (fun x d => w x.2 d) habc0
    (fun x d => hw.1 x.2 d) (fun x => hw.2 x.2)
  have habch := entropy_channel ab (fun x c => v x.2 c) hab0
    (fun x c => hv.1 x.2 c) (fun x => hv.2 x.2)
  change shannonEntropy abd = _ at habdh
  change shannonEntropy acd = _ at hacdh
  change shannonEntropy abcd = _ at habcdh
  change shannonEntropy abc = _ at habch
  rw [habdh, hacdh, habcdh, habch, weightw,
    weight (fun b => shannonEntropy (t b)), weight (fun b => shannonEntropy (v b))] at hcond
  have hc : marginal (fun x : γ × α => ac (x.2, x.1)) =
      marginal (fun x : γ × β => bc (x.2, x.1)) := by
    funext c
    unfold marginal
    dsimp only [ac, bc, s, r, mixtureJoint]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  have hd : marginal (fun x : δ × α => ad (x.2, x.1)) =
      marginal (fun x : δ × β => bd (x.2, x.1)) := by
    funext d
    unfold marginal
    dsimp only [ad, bd, z, r, mixtureJoint]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  have hbch := entropy_channel r v hr0 hv.1 hv.2
  have hbdh := entropy_channel r t hr0 ht0 ht1
  change mutualInformation bc + mutualInformation ad ≥ mutualInformation bd + mutualInformation ac
  rw [mutual_information_eq_entropy_sub bc hbc0,
    mutual_information_eq_entropy_sub ad had0,
    mutual_information_eq_entropy_sub bd hbd0,
    mutual_information_eq_entropy_sub ac hac0,
    mixtureJoint_marginal_eq_weight r v hv.2,
    mixtureJoint_marginal_eq_weight p z hz1,
    mixtureJoint_marginal_eq_weight r t ht1,
    mixtureJoint_marginal_eq_weight p s hs1, hc, hd]
  change shannonEntropy bc = _ at hbch
  change shannonEntropy bd = _ at hbdh
  rw [hbch, hbdh]
  linarith

private theorem chain_rectangle {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (p : α 0 → ℝ) (k : ∀ t, α t → α (t + 1) → ℝ)
    (hp : (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1)
    (a b c d : ℕ) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hk : ∀ u, u < d → (∀ x y, 0 ≤ k u x y) ∧ ∀ x, ∑ y, k u x y = 1) :
    mutualInformation (pairLaw p k b c hbc) +
      mutualInformation (pairLaw p k a d (by omega)) ≥
    mutualInformation (pairLaw p k b d (by omega)) +
      mutualInformation (pairLaw p k a c (by omega)) := by
  have h := four_point_rectangle (positionLaw p k a)
    (composedTransition k a b hab) (composedTransition k b c hbc)
    (composedTransition k c d hcd)
    (position_is_law p k a hp (fun u hu => hk u (by omega)))
    (composed_stochastic k a b hab (fun u _ hu => hk u (by omega)))
    (composed_stochastic k b c hbc (fun u _ hu => hk u (by omega)))
    (composed_stochastic k c d hcd (fun u _ hu => hk u hu))
  simp_rw [← composed_comp k b c d hbc hcd,
    ← composed_comp k a b d hab (hbc.trans hcd),
    ← composed_comp k a b c hab hbc, ← position_transport p k a b hab] at h
  exact h

private theorem monge_permutation (n : ℕ) (m : Fin n → Fin n → ℝ)
    (hm : ∀ i j a b, i < j → a < b → m i a + m j b ≥ m i b + m j a)
    (f : Equiv.Perm (Fin n)) : (∑ i, m i (f i)) ≤ ∑ i, m i i := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    let k : Fin (n + 1) := f.symm 0
    let g : Equiv.Perm (Fin (n + 1)) := (Equiv.swap 0 k).trans f
    have hfk : f k = 0 := f.apply_symm_apply 0
    have hg0 : g 0 = 0 := by
      change f (Equiv.swap 0 k 0) = 0
      rw [Equiv.swap_apply_left, hfk]
    have hgk : g k = f 0 := by
      change f (Equiv.swap 0 k k) = f 0
      rw [Equiv.swap_apply_right]
    have hgi (i : Fin (n + 1)) (hi : i ≠ 0) (hik : i ≠ k) : g i = f i := by
      change f (Equiv.swap 0 k i) = f i
      rw [Equiv.swap_apply_of_ne_of_ne hi hik]
    have hgain : (∑ i, m i (f i)) ≤ ∑ i, m i (g i) := by
      by_cases hk : k = 0
      · have hgf : g = f := by simp only [g, hk, Equiv.swap_self, Equiv.refl_trans]
        rw [hgf]
      · have hf : f 0 ≠ 0 := by
          intro hf
          exact hk (f.injective (hfk.trans hf.symm))
        have hrectangle := hm 0 k 0 (f 0)
          (Fin.pos_iff_ne_zero.mpr hk) (Fin.pos_iff_ne_zero.mpr hf)
        have hdifference : (∑ i, (m i (g i) - m i (f i))) =
            (m 0 0 - m 0 (f 0)) + (m k (f 0) - m k 0) := by
          calc
            (∑ i, (m i (g i) - m i (f i))) =
                (∑ i : Fin (n + 1), if i = 0 then m 0 0 - m 0 (f 0) else 0) +
                (∑ i : Fin (n + 1), if i = k then m k (f 0) - m k 0 else 0) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro i _
              by_cases hi : i = 0
              · subst i
                simp only [hg0, ite_true, Ne.symm hk, ite_false, add_zero]
              · by_cases hik : i = k
                · subst i
                  simp only [hk, ite_false, hgk, hfk, ite_true, zero_add]
                · rw [hgi i hi hik]
                  simp only [hi, hik, ite_false, sub_self, add_zero]
            _ = _ := by simp
        rw [Finset.sum_sub_distrib] at hdifference
        linarith
    obtain ⟨j, r, hr⟩ : ∃ j r, Equiv.Perm.decomposeFin.symm (j, r) = g := by
      exact ⟨(Equiv.Perm.decomposeFin g).1, (Equiv.Perm.decomposeFin g).2,
        Equiv.Perm.decomposeFin.symm_apply_apply g⟩
    have hj : j = 0 := by
      have h := congrArg (fun e : Equiv.Perm (Fin (n + 1)) => e 0) hr
      simpa only [Equiv.Perm.decomposeFin_symm_apply_zero, hg0] using h
    subst j
    have hsucc (i : Fin n) : g i.succ = (r i).succ := by
      rw [← hr]
      simp only [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self,
        Equiv.refl_apply]
    calc
      (∑ i, m i (f i)) ≤ ∑ i, m i (g i) := hgain
      _ = m 0 0 + ∑ i : Fin n, m i.succ (r i).succ := by
        rw [Fin.sum_univ_succ, hg0]
        simp_rw [hsucc]
      _ ≤ m 0 0 + ∑ i : Fin n, m i.succ i.succ :=
        add_le_add le_rfl (ih (fun i a => m i.succ a.succ)
          (fun i j a b hij hab => hm i.succ j.succ a.succ b.succ
            (Fin.succ_lt_succ_iff.mpr hij) (Fin.succ_lt_succ_iff.mpr hab)) r)
      _ = ∑ i, m i i := (Fin.sum_univ_succ (fun i : Fin (n + 1) => m i i)).symm

/-- The classical Markov monogamy inequalities hold for every size and every permutation. -/
theorem result : claim := by
  intro n α inst p k hp hk f
  apply monge_permutation n
    (fun i a => mutualInformation (pairLaw p k (n - 1 - i.val) (n + a.val) (by omega)))
    ?_ f
  intro i j a b hij hab
  exact chain_rectangle p k hp (n - 1 - j.val) (n - 1 - i.val)
    (n + a.val) (n + b.val) (by omega) (by omega) (by omega)
    (fun u hu => hk u (by have hb := b.isLt; omega))

end D5.S3.Entropy.MarkovMonogamyPermutationInequality
