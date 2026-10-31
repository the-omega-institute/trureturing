/- GID: D5/S3/TotalVariation/TreeMarkovStability
   generality: I
   mirror-B: D5/B/S3/TotalVariation/TreeMarkovStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/TotalVariation/TreeMarkovStability.SmallerEdgeCoefficient; result=D5/S3/TotalVariation/TreeMarkovStability.edge_coefficient_one_sharp; claim=D5/S3/TotalVariation/TreeMarkovStability.SmallerEdgeCoefficient
   digest: Actual finite-tree Markov laws have degree-weighted TV stability and sharp edge coefficient one. -/

import D5.S3.TotalVariation.Metric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import D5.S3.Entropy.Forgetting.PushforwardComposition
import D5.S3.Entropy.Forgetting.CompletionEntropyMinimality
import D5.S3.Divergence.ChainRule

/-! Finite normalized tree replacement stability and sharpness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.TotalVariation.TreeMarkovStability

open scoped BigOperators
open D5.S3.TotalVariation.Pinsker (totalVariation)
open D5.S3.TotalVariation.Metric

private def diagonalLaw : Bool × Bool → ℝ
  | (false, false) => 1 / 2
  | (true, true) => 1 / 2
  | _ => 0

private def antidiagonalLaw : Bool × Bool → ℝ
  | (false, true) => 1 / 2
  | (true, false) => 1 / 2
  | _ => 0

private theorem diagonalLaw_nonnegative : ∀ z, 0 ≤ diagonalLaw z := by
  intro z
  rcases z with ⟨a, b⟩ <;> cases a <;> cases b <;> norm_num [diagonalLaw]

private theorem antidiagonalLaw_nonnegative : ∀ z, 0 ≤ antidiagonalLaw z := by
  intro z
  rcases z with ⟨a, b⟩ <;> cases a <;> cases b <;> norm_num [antidiagonalLaw]


open scoped Classical

local instance (priority := 2000) configurationFintype {V : Type*} [Fintype V]
    {X : V → Type*} [∀ v, Fintype (X v)] : Fintype (∀ v, X v) := Fintype.ofFinite _

open D5.S3.Entropy.Forgetting.CapacityMonotone (pushforward)
open D5.S3.Entropy.Forgetting.PushforwardComposition (pushforward_comp)
open D5.S3.Divergence.ChainRule (marginal conditional)

/-- A conditional row completed by a prescribed probability row at zero mass. -/
def completedConditional {A B : Type*} [Fintype B]
    (π : A × B → ℝ) (fallback : B → ℝ) (a : A) (b : B) : ℝ :=
  if marginal π a = 0 then fallback b else conditional π a b

private theorem completed_conditional_properties {A B : Type*} [Fintype B]
    (π : A × B → ℝ) (fallback : B → ℝ)
    (hπ : ∀ z, 0 ≤ π z) (hf : (∀ b, 0 ≤ fallback b) ∧ ∑ b, fallback b = 1) :
    (∀ a b, 0 ≤ completedConditional π fallback a b) ∧
    (∀ a, ∑ b, completedConditional π fallback a b = 1) ∧
    (∀ a b, marginal π a * completedConditional π fallback a b = π (a,b)) := by
  have hm (a : A) : 0 ≤ marginal π a := Finset.sum_nonneg fun b _ => hπ (a,b)
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    unfold completedConditional
    split_ifs
    · exact hf.1 b
    · exact div_nonneg (hπ _) (hm a)
  · intro a
    by_cases h : marginal π a = 0
    · simp [completedConditional, h, hf.2]
    · simp only [completedConditional, if_neg h, conditional]
      rw [← Finset.sum_div]
      exact div_self h
  · intro a b
    by_cases h : marginal π a = 0
    · have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => hπ (a,c))).mp h b
        (Finset.mem_univ b)
      simp [completedConditional, h, hz]
    · simp only [completedConditional, if_neg h, conditional]
      exact mul_div_cancel₀ _ h

/-- Retain the old configuration and add one new coordinate through its parent. -/
def extend {Ω A B : Type*} (p : Ω → ℝ) (f : Ω → A) (K : A → B → ℝ) : Ω × B → ℝ :=
  fun z => p z.1 * K (f z.1) z.2

private theorem extend_same_kernel {Ω A B : Type*} [Fintype Ω] [Fintype B]
    (p q : Ω → ℝ) (f : Ω → A) (K : A → B → ℝ)
    (hK : (∀ a b, 0 ≤ K a b) ∧ ∀ a, ∑ b, K a b = 1) :
    totalVariation (extend p f K) (extend q f K) = totalVariation p q := by
  unfold totalVariation extend
  rw [Fintype.sum_prod_type]
  simp_rw [← sub_mul, abs_mul, abs_of_nonneg (hK.1 _ _), ← Finset.mul_sum, hK.2,
    mul_one]

private theorem sum_pushforward_mul {Ω A : Type*} [Fintype Ω] [Fintype A]
    (p : Ω → ℝ) (f : Ω → A) (h : A → ℝ) :
    (∑ a, pushforward f p a * h a) = ∑ x, p x * h (f x) := by
  simp only [pushforward, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

private theorem extend_change_kernel {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    (q : Ω → ℝ) (f : Ω → A) (K L : A → B → ℝ) (hq : ∀ x, 0 ≤ q x) :
    totalVariation (extend q f K) (extend q f L) =
      totalVariation (fun z : A × B => pushforward f q z.1 * K z.1 z.2)
        (fun z => pushforward f q z.1 * L z.1 z.2) := by
  have hn (a : A) : 0 ≤ pushforward f q a := by
      exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp_all [pushforward]
  unfold totalVariation extend
  simp_rw [Fintype.sum_prod_type, ← mul_sub, abs_mul, abs_of_nonneg (hq _),
    abs_of_nonneg (hn _), ← Finset.mul_sum]
  rw [sum_pushforward_mul]

/-- The actual leaf extension estimate, with its parent laws obtained as marginals. -/
private theorem leaf_extension_bound {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    (p q : Ω → ℝ) (f : Ω → A) (π χ : A × B → ℝ) (K L : A → B → ℝ)
    (hq : ∀ x, 0 ≤ q x)
    (hK : (∀ a b, 0 ≤ K a b) ∧ ∀ a, ∑ b, K a b = 1)
    (hq' : pushforward f q = marginal χ)
    (hπ : ∀ a b, marginal π a * K a b = π (a,b))
    (hχ : ∀ a b, marginal χ a * L a b = χ (a,b)) :
    totalVariation (extend p f K) (extend q f L) ≤
      totalVariation p q + totalVariation π χ + totalVariation (marginal π) (marginal χ) := by
  let νK : A × B → ℝ := fun z => marginal χ z.1 * K z.1 z.2
  have h1 := total_variation_triangle (extend p f K) (extend q f K) (extend q f L)
  rw [extend_same_kernel p q f K hK, extend_change_kernel q f K L hq] at h1
  rw [hq'] at h1
  have hχfun : (fun z : A × B => marginal χ z.1 * L z.1 z.2) = χ :=
    funext fun z => hχ z.1 z.2
  rw [hχfun] at h1
  have h2 := total_variation_triangle νK π χ
  have h3 : totalVariation νK π = totalVariation (marginal χ) (marginal π) := by
    have he : π = extend (marginal π) id K := (funext fun z : A × B => hπ z.1 z.2).symm
    conv_lhs => rw [he]
    exact extend_same_kernel _ _ id K hK
  rw [h3, total_variation_comm (marginal χ) (marginal π)] at h2
  exact le_trans h1 (by dsimp [νK] at h2; linarith)

private theorem extend_marginals {Ω A B : Type*} [Fintype Ω] [Fintype B]
    (p : Ω → ℝ) (f : Ω → A) (K : A → B → ℝ)
    (hK : ∀ a, ∑ b, K a b = 1) :
    pushforward Prod.fst (extend p f K) = p ∧
      pushforward (fun z : Ω × B => (f z.1,z.2)) (extend p f K) =
        fun z : A × B => pushforward f p z.1 * K z.1 z.2 := by
  constructor
  · funext x
    simp only [pushforward, extend, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single x]
    · simp [← Finset.mul_sum, hK]
    · intro y _ hy
      simp [hy]
    · simp
  · funext z
    rcases z with ⟨a,b⟩
    simp only [pushforward, extend, Fintype.sum_prod_type, Prod.mk.injEq]
    simp_rw [show ∀ x : Ω, (∑ y : B, if f x = a ∧ y = b then p x * K (f x) y else 0) =
      if f x = a then p x * K a b else 0 by
      intro x; by_cases hx : f x = a <;> simp [hx]]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp_all

/-- A finite tree is reduced to an edge by removing leaves; vertices are never identified. -/
inductive TreeOrder : {V : Type} → SimpleGraph V → Type 1
  | edge {V : Type} {G : SimpleGraph V} (r s : V) (hne : r ≠ s)
      (cover : ∀ v, v = r ∨ v = s) (adj : G.Adj r s) : TreeOrder G
  | leaf {V : Type} {G : SimpleGraph V} (v : V) (u : {w : V // w ≠ v})
      (adj : ∀ w, G.Adj v w ↔ w = u.val)
      (old : TreeOrder (G.induce {w | w ≠ v})) : TreeOrder G

/-- The initial endpoint of the oriented root edge. -/
def TreeOrder.root : ∀ {V : Type} {G : SimpleGraph V}, TreeOrder G → V
  | _, _, .edge r _ _ _ _ => r
  | _, _, .leaf _ _ _ old => (TreeOrder.root old).val

private theorem tree_order_exists {V : Type} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsTree) (hV : 2 ≤ Fintype.card V) (root : V) :
    ∃ t : TreeOrder G, t.root = root := by
  have aux : ∀ n : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n → G.IsTree → 2 ≤ n → ∀ root : V, ∃ t : TreeOrder G, t.root = root := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ G hn ht hn2 root
      letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨a,b,hab,ha,hb⟩ := ht.exists_ne_and_degree_eq_one
      obtain ⟨v,hvr,hv⟩ : ∃ v : V, v ≠ root ∧ G.degree v = 1 := by
        by_cases h : a = root
        · exact ⟨b, by intro he; exact hab (h.trans he.symm), hb⟩
        · exact ⟨a,h,ha⟩
      obtain ⟨u, hu, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
      have huv : u ≠ v := G.ne_of_adj hu.symm
      by_cases htwo : n = 2
      · have cover : ∀ w : V, w = v ∨ w = u := by
          intro w
          by_contra h
          have hwv : w ≠ v := fun hh => h (Or.inl hh)
          have hwu : w ≠ u := fun hh => h (Or.inr hh)
          have h3 := Finset.card_le_card (Finset.subset_univ ({v,u,w} : Finset V))
          have hc : ({v,u,w} : Finset V).card = 3 := by
            simp [huv, hwv, hwu, Ne.symm huv, Ne.symm hwv, Ne.symm hwu]
          rw [hc, Finset.card_univ] at h3
          omega
        have hur : u = root := ((cover root).resolve_left (Ne.symm hvr)).symm
        exact ⟨TreeOrder.edge u v huv (fun w => (cover w).symm) hu.symm, hur⟩
      · let W := {w : V // w ≠ v}
        let G' : SimpleGraph W := G.induce {w | w ≠ v}
        have hcard : Fintype.card W + 1 = Fintype.card V := by
          change Fintype.card {w : V // w ≠ v} + 1 = Fintype.card V
          rw [Fintype.card_subtype_compl]
          simp only [Fintype.card_subtype_eq]
          omega
        have ht' : G'.IsTree :=
          ⟨by
            have hs : ({v}ᶜ : Set V) = {w | w ≠ v} := by ext w; simp
            have hh := ht.connected.induce_compl_singleton_of_degree_eq_one hv
            rw [hs] at hh
            exact hh,
            ht.isAcyclic.induce _⟩
        obtain ⟨t,hr⟩ := ih (Fintype.card W) (by omega) W G' rfl ht' (by omega)
          ⟨root, Ne.symm hvr⟩
        have hleaf : ∀ w, G.Adj v w ↔ w = u := by
          intro w
          exact ⟨fun hw => huniq w hw, fun hw => hw ▸ hu⟩
        refine ⟨TreeOrder.leaf v ⟨u,huv⟩ hleaf t, ?_⟩
        simpa only [TreeOrder.root] using congrArg Subtype.val hr
  exact aux (Fintype.card V) V G rfl hG hV root


/-- Node laws share actual coordinates; each oriented edge has its prescribed two marginals. -/
structure Family {V : Type} (G : SimpleGraph V) (X : V → Type) [∀ v, Fintype (X v)] where
  node : ∀ v, X v → ℝ
  node_nonnegative : ∀ v a, 0 ≤ node v a
  node_total : ∀ v, ∑ a, node v a = 1
  edge : ∀ i j, X i × X j → ℝ
  edge_nonnegative : ∀ i j, G.Adj i j → ∀ z, 0 ≤ edge i j z
  edge_left : ∀ i j, G.Adj i j → marginal (edge i j) = node i
  edge_right : ∀ i j, G.Adj i j → ∀ b, ∑ a, edge i j (a,b) = node j b
  edge_swap : ∀ i j, G.Adj i j → ∀ a b, edge i j (a,b) = edge j i (b,a)

namespace Family

def restrict {V : Type} {G : SimpleGraph V} {X : V → Type} [∀ v, Fintype (X v)]
    (F : Family G X) (v : V) :
    Family (G.induce {w | w ≠ v}) (fun w : {w : V // w ≠ v} => X w) where
  node w := F.node w
  node_nonnegative w := F.node_nonnegative w
  node_total w := F.node_total w
  edge i j := F.edge i j
  edge_nonnegative i j h := F.edge_nonnegative i j h
  edge_left i j h := F.edge_left i j h
  edge_right i j h := F.edge_right i j h
  edge_swap i j h := F.edge_swap i j h

end Family

/-- The joint mass obtained by the actual tree conditional factorization. -/
def treeMass : ∀ {V : Type} {G : SimpleGraph V} (t : TreeOrder G)
    {X : V → Type} [∀ v, Fintype (X v)], Family G X → (∀ v, X v) → ℝ
  | _, _, .edge r s _ _ _, _, _, F => fun x => F.edge r s (x r,x s)
  | _, _, .leaf v u _ old, _, _, F => fun x =>
      treeMass old (F.restrict v) (fun w => x w) *
        completedConditional (F.edge u v) (F.node v) (x u) (x v)

private def pairEquiv {V : Type} {X : V → Type} (r s : V) (hne : r ≠ s)
    (cover : ∀ v, v = r ∨ v = s) : (∀ v, X v) ≃ X r × X s := by
  refine {
    toFun := fun x => (x r,x s)
    invFun := fun z v => if h : v = r then (congrArg X h).symm ▸ z.1
      else (congrArg X ((cover v).resolve_left h)).symm ▸ z.2
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    funext v
    rcases cover v with h | h <;> subst v <;> simp [hne, Ne.symm hne]
  · intro z
    simp [hne, Ne.symm hne]

private theorem pushforward_equiv {Ω Ξ A : Type*} [Fintype Ω] [Fintype Ξ]
    (e : Ω ≃ Ξ) (p : Ξ → ℝ) (f : Ω → A) :
    pushforward f (fun x => p (e x)) = pushforward (f ∘ e.symm) p := by
  funext a
  simpa [pushforward] using Equiv.sum_comp e
    (fun y => if f (e.symm y) = a then p y else 0)

private theorem pushforward_fst {A B : Type*} [Fintype A] [Fintype B]
    (π : A × B → ℝ) : pushforward Prod.fst π = marginal π := by
  exact (D5.S3.Entropy.Forgetting.CompletionEntropyMinimality.marginal_eq_pushforward_fst π).symm

private theorem pushforward_snd {A B : Type*} [Fintype A] [Fintype B]
    (π : A × B → ℝ) : pushforward Prod.snd π = fun b => ∑ a, π (a,b) := by
  funext b
  simp [pushforward, Fintype.sum_prod_type]

private theorem extend_old_readout {Ω A B C : Type*} [Fintype Ω] [Fintype B]
    (p : Ω → ℝ) (f : Ω → A) (K : A → B → ℝ) (hK : ∀ a, ∑ b, K a b = 1)
    (g : Ω → C) :
    pushforward (fun z : Ω × B => g z.1) (extend p f K) = pushforward g p := by
  calc
    _ = pushforward g (pushforward Prod.fst (extend p f K)) :=
      (pushforward_comp (extend p f K) Prod.fst g).symm
    _ = _ := by rw [(extend_marginals p f K hK).1]

private theorem tree_law_properties : ∀ {V : Type} {G : SimpleGraph V} (t : TreeOrder G)
    [Fintype V] (X : V → Type) [∀ v, Fintype (X v)] (F : Family G X),
    (∀ x, 0 ≤ treeMass t F x) ∧ (∑ x, treeMass t F x) = 1 ∧
    (∀ i, pushforward (fun x : ∀ v, X v => x i) (treeMass t F) = F.node i) ∧
    (∀ i j, G.Adj i j →
      pushforward (fun x : ∀ v, X v => (x i,x j)) (treeMass t F) = F.edge i j) := by
  intro V G t
  induction t with
  | @edge V G r s hne cover hadj =>
    intro _ X _ F
    let e := pairEquiv (X := X) r s hne cover
    have hm : treeMass (.edge r s hne cover hadj) F = fun x => F.edge r s (e x) := rfl
    have hleft : pushforward (fun x : ∀ v, X v => x r) (treeMass (.edge r s hne cover hadj) F) =
        F.node r := by
      rw [hm, pushforward_equiv]
      have he : (fun x : ∀ v, X v => x r) ∘ e.symm = Prod.fst := by
        funext z
        exact congrArg Prod.fst (e.apply_symm_apply z)
      rw [he, pushforward_fst, F.edge_left r s hadj]
    have hright : pushforward (fun x : ∀ v, X v => x s) (treeMass (.edge r s hne cover hadj) F) =
        F.node s := by
      rw [hm, pushforward_equiv]
      have he : (fun x : ∀ v, X v => x s) ∘ e.symm = Prod.snd := by
        funext z
        exact congrArg Prod.snd (e.apply_symm_apply z)
      rw [he, pushforward_snd]
      exact funext (F.edge_right r s hadj)
    refine ⟨fun x => F.edge_nonnegative r s hadj _, ?_, ?_, ?_⟩
    · rw [hm]
      change (∑ x, F.edge r s (e x)) = 1
      rw [Equiv.sum_comp e, Fintype.sum_prod_type]
      change (∑ a, marginal (F.edge r s) a) = 1
      rw [F.edge_left r s hadj, F.node_total r]
    · intro i
      rcases cover i with h | h <;> subst i <;> assumption
    · intro i j hij
      rcases cover i with h | h <;> rcases cover j with h' | h' <;> subst i <;> subst j
      · exact (G.irrefl hij).elim
      · rw [hm, pushforward_equiv]
        have he : (fun x : ∀ v, X v => (x r,x s)) ∘ e.symm = id := by funext z; exact e.apply_symm_apply z
        rw [he]
        funext z
        unfold pushforward
        rw [Finset.sum_eq_single z]
        · simp
        · intro y _ hy
          simp [hy]
        · simp
      · rw [hm, pushforward_equiv]
        have he : (fun x : ∀ v, X v => (x s,x r)) ∘ e.symm = Prod.swap := by
          funext z
          exact congrArg Prod.swap (e.apply_symm_apply z)
        rw [he]
        funext z
        rw [pushforward]
        rw [Finset.sum_eq_single z.swap]
        · simp [F.edge_swap r s hadj]
        · intro y _ hy
          rw [if_neg]
          intro hh
          exact hy (by simpa using congrArg Prod.swap hh)
        · simp
      · exact (G.irrefl hij).elim
  | @leaf V G v u hadj old ih =>
    intro _ X _ F
    let W := {w : V // w ≠ v}
    let Y : W → Type := fun w => X w
    let p := treeMass old (F.restrict v)
    have h := ih Y (F.restrict v)
    let K := completedConditional (F.edge u v) (F.node v)
    have huv : G.Adj u.val v := (hadj u).mpr rfl |>.symm
    have hk := completed_conditional_properties (F.edge u v) (F.node v)
      (F.edge_nonnegative u v huv) ⟨F.node_nonnegative v, F.node_total v⟩
    let e : (∀ w, X w) ≃ (∀ w : W, Y w) × X v :=
      (Equiv.piSplitAt v X).trans (Equiv.prodComm _ _)
    have hm : treeMass (.leaf v u hadj old) F = fun x => extend p (fun y => y u) K (e x) := rfl
    have hp : pushforward (fun y : ∀ w : W, Y w => y u) p = marginal (F.edge u v) := by
      rw [F.edge_left u v huv]
      exact h.2.2.1 u
    have hedge : pushforward (fun z : (∀ w : W, Y w) × X v => (z.1 u,z.2))
        (extend p (fun y => y u) K) = F.edge u v := by
      have he := (extend_marginals p (fun y => y u) K hk.2.1).2
      have hr : (fun z : X u × X v => pushforward (fun y => y u) p z.1 * K z.1 z.2) = F.edge u v := by
        funext z
        calc
          _ = marginal (F.edge u v) z.1 * K z.1 z.2 := by
            congr 1
            convert congrFun hp z.1 using 1 <;> congr!
          _ = _ := hk.2.2 z.1 z.2
      exact he.trans hr
    have hnodeold (i : W) :
        pushforward (fun x : ∀ w, X w => x i) (treeMass (.leaf v u hadj old) F) = F.node i := by
      rw [hm, pushforward_equiv]
      have he : (fun x : ∀ w, X w => x i) ∘ e.symm = fun z => z.1 i := by
        funext z
        have hh := congrArg (fun y : (∀ w : W, Y w) × X v => y.1 i) (e.apply_symm_apply z)
        exact hh
      rw [he]
      exact (extend_old_readout p (fun y => y u) K hk.2.1 (fun y => y i)).trans (h.2.2.1 i)
    have hnodenew : pushforward (fun x : ∀ w, X w => x v)
        (treeMass (.leaf v u hadj old) F) = F.node v := by
      rw [hm, pushforward_equiv]
      have he : (fun x : ∀ w, X w => x v) ∘ e.symm = Prod.snd := by
        funext z
        exact congrArg Prod.snd (e.apply_symm_apply z)
      rw [he]
      have hh := congrArg (pushforward Prod.snd) hedge
      rw [pushforward_comp] at hh
      change pushforward Prod.snd (extend p (fun y => y u) K) = F.node v
      calc
        _ = pushforward Prod.snd (F.edge u v) := hh
        _ = _ := by rw [pushforward_snd]; exact funext (F.edge_right u v huv)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x
      exact mul_nonneg (h.1 _) (hk.1 _ _)
    · rw [hm]
      change (∑ x, extend p (fun y => y u) K (e x)) = 1
      rw [Equiv.sum_comp e, Fintype.sum_prod_type]
      simp only [extend]
      calc
        _ = ∑ y, p y * ∑ b, K (y u) b := by
          simp_rw [← Finset.mul_sum]
          congr!
        _ = ∑ y, p y := by
          apply Finset.sum_congr rfl
          intro y _
          rw [show (∑ b, K (y u) b) = 1 from hk.2.1 (y u), mul_one]
        _ = 1 := h.2.1
    · intro i
      by_cases hi : i = v
      · subst i; exact hnodenew
      · exact hnodeold ⟨i,hi⟩
    · intro i j hij
      by_cases hi : i = v
      · subst i
        have hj : j = u.val := (hadj j).mp hij
        subst j
        rw [hm, pushforward_equiv]
        have he : (fun x : ∀ w, X w => (x v,x u)) ∘ e.symm =
            fun z => (z.2,z.1 u) := by
          funext z
          have hh := e.apply_symm_apply z
          exact congrArg (fun y : (∀ w : W, Y w) × X v => (y.2,y.1 u)) hh
        rw [he]
        have hh := congrArg (pushforward Prod.swap) hedge
        rw [pushforward_comp] at hh
        change pushforward (fun z => (z.2,z.1 u)) (extend p (fun y => y u) K) = F.edge v u
        calc
          _ = pushforward Prod.swap (F.edge u v) := hh
          _ = _ := by
            funext z
            simp only [pushforward]
            rw [Finset.sum_eq_single z.swap]
            · simp [F.edge_swap u v huv]
            · intro y _ hy
              rw [if_neg]
              exact fun h => hy (by simpa using congrArg Prod.swap h)
            · simp
      · by_cases hj : j = v
        · subst j
          have hi' : i = u.val := (hadj i).mp hij.symm
          subst i
          rw [hm, pushforward_equiv]
          have he : (fun x : ∀ w, X w => (x u,x v)) ∘ e.symm =
              fun z => (z.1 u,z.2) := by
            funext z
            exact congrArg (fun y : (∀ w : W, Y w) × X v => (y.1 u,y.2)) (e.apply_symm_apply z)
          rw [he]
          exact hedge
        · rw [hm, pushforward_equiv]
          have he : (fun x : ∀ w, X w => (x i,x j)) ∘ e.symm =
              fun z => (z.1 ⟨i,hi⟩,z.1 ⟨j,hj⟩) := by
            funext z
            exact congrArg (fun y : (∀ w : W, Y w) × X v => (y.1 ⟨i,hi⟩,y.1 ⟨j,hj⟩))
              (e.apply_symm_apply z)
          rw [he]
          exact (extend_old_readout p (fun y => y u) K hk.2.1
            (fun y => (y ⟨i,hi⟩,y ⟨j,hj⟩))).trans (h.2.2.2 ⟨i,hi⟩ ⟨j,hj⟩ hij)


private theorem tv_equiv {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (e : Ω ≃ Ξ) (p q : Ξ → ℝ) :
    totalVariation (fun x => p (e x)) (fun x => q (e x)) = totalVariation p q := by
  unfold totalVariation
  congr 1
  exact Equiv.sum_comp e (fun z => |p z - q z|)

private theorem sum_split {V : Type} [Fintype V] (v : V) (f : V → ℝ) :
    (∑ w, f w) = f v + ∑ w : {w : V // w ≠ v}, f w := by
  exact Fintype.sum_eq_add_sum_subtype_ne f v

private theorem sum_pair {V : Type} [Fintype V] (r s : V) (hne : r ≠ s)
    (cover : ∀ v, v = r ∨ v = s) (f : V → ℝ) :
    (∑ v, f v) = f r + f s := by
  have h (w : {w : V // w ≠ r}) : w.val = s := (cover w).resolve_left w.property
  letI : Subsingleton {w : V // w ≠ r} := ⟨fun a b => Subtype.ext ((h a).trans (h b).symm)⟩
  rw [sum_split r]
  rw [Fintype.sum_subsingleton (fun w : {w : V // w ≠ r} => f w) ⟨s,Ne.symm hne⟩]

/-- The sum over both orientations of each graph edge. -/
def orientedSum {V : Type} [Fintype V] (G : SimpleGraph V) (c : V → V → ℝ) : ℝ :=
  by exact ∑ i, ∑ j, if G.Adj i j then c i j else 0

private theorem oriented_sum_leaf {V : Type} [Fintype V] (G : SimpleGraph V)
    (v : V) (u : {w : V // w ≠ v}) (hadj : ∀ w, G.Adj v w ↔ w = u.val)
    (c : V → V → ℝ) :
    orientedSum G c = orientedSum (G.induce {w | w ≠ v}) (fun i j => c i j) +
      c v u + c u v := by
  have hr (w : V) : G.Adj w v ↔ w = u.val := by rw [G.adj_comm]; exact hadj w
  have rowv : (∑ j, if G.Adj v j then c v j else 0) = c v u := by simp [hadj]
  have roww (w : {w : V // w ≠ v}) :
      (∑ j, if G.Adj w.val j then c w j else 0) =
        (if w = u then c w v else 0) +
          ∑ j : {w : V // w ≠ v}, if G.Adj w.val j.val then c w j else 0 := by
    rw [sum_split v]
    congr 1
    simp [hr, Subtype.ext_iff]
  unfold orientedSum
  rw [sum_split v, rowv]
  simp_rw [roww]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change c v u + (c u v + (∑ i : {w : V // w ≠ v}, ∑ j : {w : V // w ≠ v},
    if G.Adj i.val j.val then c i j else 0)) =
    (∑ i : {w : V // w ≠ v}, ∑ j : {w : V // w ≠ v},
    if G.Adj i.val j.val then c i j else 0) + c v u + c u v
  ring

private theorem oriented_sum_edge {V : Type} [Fintype V] (G : SimpleGraph V)
    (r s : V) (hne : r ≠ s) (cover : ∀ v, v = r ∨ v = s) (hadj : G.Adj r s)
    (c : V → V → ℝ) : orientedSum G c = c r s + c s r := by
  unfold orientedSum
  rw [sum_pair r s hne cover]
  rw [sum_pair r s hne cover, sum_pair r s hne cover]
  simp [hadj, hadj.symm]

/-- Every undirected edge contributes once, since its two oriented TVs agree. -/
def edgeBudget {V : Type} [Fintype V] {G : SimpleGraph V} {X : V → Type}
    [∀ v, Fintype (X v)] (F H : Family G X) : ℝ :=
  (1 / 2 : ℝ) * orientedSum G (fun i j => totalVariation (F.edge i j) (H.edge i j))

/-- The graph degree charge uses real subtraction, with no truncated natural subtraction. -/
def nodeBudget {V : Type} [Fintype V] (G : SimpleGraph V) (d : V → ℝ) : ℝ :=
  by exact ∑ i, ((G.degree i : ℝ) - 1) * d i

private theorem node_budget_expansion {V : Type} [Fintype V] (G : SimpleGraph V)
    (d : V → ℝ) : nodeBudget G d = orientedSum G (fun i _ => d i) - ∑ i, d i := by
  have hd (i : V) : (G.degree i : ℝ) = ∑ j, if G.Adj i j then (1 : ℝ) else 0 := by
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    push_cast
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  unfold nodeBudget orientedSum
  simp_rw [sub_mul, one_mul, hd, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_sub_distrib]

private theorem node_budget_leaf {V : Type} [Fintype V] (G : SimpleGraph V)
    (v : V) (u : {w : V // w ≠ v}) (hadj : ∀ w, G.Adj v w ↔ w = u.val)
    (d : V → ℝ) :
    nodeBudget G d = nodeBudget (G.induce {w | w ≠ v}) (fun w => d w) + d u := by
  rw [node_budget_expansion, node_budget_expansion,
    oriented_sum_leaf G v u hadj, sum_split v]
  have he : (∑ w : {w : V // w ≠ v}, d w) =
      (∑ w : {w | w ≠ v}, d w) := by congr 1
  rw [he]
  ring

private theorem edge_distance_swap {V : Type} {G : SimpleGraph V} {X : V → Type}
    [∀ v, Fintype (X v)] (F H : Family G X) (i j : V) (h : G.Adj i j) :
    totalVariation (F.edge i j) (H.edge i j) = totalVariation (F.edge j i) (H.edge j i) := by
  have he := tv_equiv (Equiv.prodComm (X i) (X j)) (F.edge j i) (H.edge j i)
  convert he using 1
  · exact congrArg₂ totalVariation (funext fun z => (F.edge_swap i j h z.1 z.2))
      (funext fun z => (H.edge_swap i j h z.1 z.2))

private theorem edge_budget_leaf {V : Type} [Fintype V] {G : SimpleGraph V}
    {X : V → Type} [∀ v, Fintype (X v)] (F H : Family G X)
    (v : V) (u : {w : V // w ≠ v}) (hadj : ∀ w, G.Adj v w ↔ w = u.val) :
    edgeBudget F H = edgeBudget (F.restrict v) (H.restrict v) +
      totalVariation (F.edge u v) (H.edge u v) := by
  unfold edgeBudget
  rw [oriented_sum_leaf G v u hadj,
    edge_distance_swap F H v u ((hadj u).mpr rfl)]
  dsimp only [Family.restrict]
  ring

set_option maxHeartbeats 1000000 in
-- The dependent leaf induction elaborates both restricted state families and their TV budgets.
private theorem tree_stability : ∀ {V : Type} {G : SimpleGraph V} (t : TreeOrder G)
    [Fintype V] (X : V → Type) [∀ v, Fintype (X v)] (F H : Family G X),
    totalVariation (treeMass t F) (treeMass t H) ≤ edgeBudget F H +
      nodeBudget G (fun i => totalVariation (F.node i) (H.node i)) := by
  intro V G t
  induction t with
  | @edge V G r s hne cover hadj =>
    intro _ X _ F H
    let e := pairEquiv (X := X) r s hne cover
    have htv : totalVariation (treeMass (.edge r s hne cover hadj) F)
        (treeMass (.edge r s hne cover hadj) H) = totalVariation (F.edge r s) (H.edge r s) :=
      tv_equiv e _ _
    have hn : nodeBudget G (fun i => totalVariation (F.node i) (H.node i)) = 0 := by
      rw [node_budget_expansion, oriented_sum_edge G r s hne cover hadj,
        sum_pair r s hne cover]
      ring
    rw [htv, hn, add_zero]
    unfold edgeBudget
    rw [oriented_sum_edge G r s hne cover hadj, edge_distance_swap F H s r hadj.symm]
    linarith
  | @leaf V G v u hadj old ih =>
    intro _ X _ F H
    let W := {w : V // w ≠ v}
    let Y : W → Type := fun w => X w
    let p := treeMass old (F.restrict v)
    let q := treeMass old (H.restrict v)
    have hq := tree_law_properties old Y (H.restrict v)
    let K := completedConditional (F.edge u v) (F.node v)
    let L := completedConditional (H.edge u v) (H.node v)
    have huv : G.Adj u.val v := ((hadj u).mpr rfl).symm
    have hk := completed_conditional_properties (F.edge u v) (F.node v)
      (F.edge_nonnegative u v huv) ⟨F.node_nonnegative v, F.node_total v⟩
    have hl := completed_conditional_properties (H.edge u v) (H.node v)
      (H.edge_nonnegative u v huv) ⟨H.node_nonnegative v, H.node_total v⟩
    let e : (∀ w, X w) ≃ (∀ w : W, Y w) × X v :=
      (Equiv.piSplitAt v X).trans (Equiv.prodComm _ _)
    have htv : totalVariation (treeMass (.leaf v u hadj old) F)
        (treeMass (.leaf v u hadj old) H) =
        totalVariation (extend p (fun y => y u) K) (extend q (fun y => y u) L) :=
      tv_equiv e (extend p (fun y => y u) K) (extend q (fun y => y u) L)
    have hb := leaf_extension_bound p q (fun y => y u) (F.edge u v) (H.edge u v) K L
      hq.1 ⟨hk.1,hk.2.1⟩
      (by rw [H.edge_left u v huv]; exact hq.2.2.1 u) hk.2.2 hl.2.2
    rw [F.edge_left u v huv, H.edge_left u v huv] at hb
    rw [htv, edge_budget_leaf F H v u hadj, node_budget_leaf G v u hadj]
    have hi := ih Y (F.restrict v) (H.restrict v)
    have hbr : totalVariation (extend p (fun y => y u) K) (extend q (fun y => y u) L) ≤
        totalVariation p q + totalVariation (F.edge u v) (H.edge u v) +
          totalVariation (F.node u) (H.node u) := by
      convert hb using 1 <;> congr!
    have hir : totalVariation p q ≤ edgeBudget (F.restrict v) (H.restrict v) +
        nodeBudget (G.induce {w | w ≠ v}) (fun w => totalVariation (F.node w) (H.node w)) := by
      convert hi using 1 <;> congr!
    linarith only [hbr, hir]


/-- A root-node marginal followed by the actual oriented conditional factors. -/
def factorMass : ∀ {V : Type} {G : SimpleGraph V} (t : TreeOrder G)
    {X : V → Type} [∀ v, Fintype (X v)],
    Family G X → (∀ i j, X i → X j → ℝ) → (∀ v, X v) → ℝ
  | _, _, .edge r s _ _ _, _, _, F, K => fun x => F.node r (x r) * K r s (x r) (x s)
  | _, _, .leaf v u _ old, _, _, F, K => fun x =>
      factorMass old (F.restrict v) (fun i j => K i j) (fun w => x w) * K u v (x u) (x v)

private theorem zero_fiber {Ω A : Type*} [Fintype Ω]
    (p : Ω → ℝ) (f : Ω → A) (hp : ∀ x, 0 ≤ p x) (x : Ω)
    (hz : pushforward f p (f x) = 0) : p x = 0 := by
  unfold pushforward at hz
  have hn (y : Ω) : 0 ≤ if f y = f x then p y else 0 := by
    split_ifs
    · exact hp y
    · exact le_rfl
  have h := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hn y)).mp hz x (Finset.mem_univ x)
  simpa using h

/-- Only positive-mass conditional rows matter; zero rows may even be arbitrary real rows. -/
private theorem tree_kernel_independence : ∀ {V : Type} {G : SimpleGraph V} (t : TreeOrder G)
    [Fintype V] (X : V → Type) [∀ v, Fintype (X v)] (F : Family G X)
    (K : ∀ i j, X i → X j → ℝ),
    (∀ i j, G.Adj i j → ∀ a b, F.node i a * K i j a b = F.edge i j (a,b)) →
    factorMass t F K = treeMass t F := by
  intro V G t
  induction t with
  | @edge V G r s hne cover hadj =>
    intro _ X _ F K hK
    funext x
    exact hK r s hadj (x r) (x s)
  | @leaf V G v u hadj old ih =>
    intro _ X _ F K hK
    have hh := ih (fun w : {w : V // w ≠ v} => X w) (F.restrict v)
      (fun i j => K i j) (fun i j h => hK i j h)
    funext x
    change factorMass old (F.restrict v) (fun i j => K i j) (fun w => x w) * K u v (x u) (x v) = _
    rw [hh]
    change treeMass old (F.restrict v) (fun w => x w) * K u v (x u) (x v) =
      treeMass old (F.restrict v) (fun w => x w) *
        completedConditional (F.edge u v) (F.node v) (x u) (x v)
    have huv : G.Adj u.val v := ((hadj u).mpr rfl).symm
    by_cases hz : F.node u (x u) = 0
    · have hprop := tree_law_properties old (fun w : {w : V // w ≠ v} => X w) (F.restrict v)
      have hzero : treeMass old (F.restrict v) (fun w => x w) = 0 := by
        apply zero_fiber _ (fun y => y u) hprop.1 (fun w => x w)
        rw [hprop.2.2.1 u]
        exact hz
      rw [hzero, zero_mul, zero_mul]
    · have hk := completed_conditional_properties (F.edge u v) (F.node v)
        (F.edge_nonnegative u v huv) ⟨F.node_nonnegative v,F.node_total v⟩
      have h1 := hk.2.2 (x u) (x v)
      rw [F.edge_left u v huv] at h1
      have he : K u v (x u) (x v) = completedConditional (F.edge u v) (F.node v) (x u) (x v) :=
        mul_left_cancel₀ hz ((hK u v huv (x u) (x v)).trans h1.symm)
      rw [he]

private theorem quotient_reconstruction {V : Type} {G : SimpleGraph V} {X : V → Type}
    [∀ v, Fintype (X v)] (F : Family G X) (K : ∀ i j, X i → X j → ℝ)
    (hK : ∀ i j, G.Adj i j → ∀ a b, F.node i a ≠ 0 →
      K i j a b = F.edge i j (a,b) / F.node i a) :
    ∀ i j, G.Adj i j → ∀ a b, F.node i a * K i j a b = F.edge i j (a,b) := by
  intro i j hij a b
  by_cases hz : F.node i a = 0
  · have hh : (∑ c, F.edge i j (a,c)) = 0 := by
      change marginal (F.edge i j) a = 0
      rw [F.edge_left i j hij, hz]
    have hcell := (Finset.sum_eq_zero_iff_of_nonneg
      (fun c _ => F.edge_nonnegative i j hij (a,c))).mp hh b (Finset.mem_univ b)
    rw [hz, zero_mul, hcell]
  · rw [hK i j hij a b hz]
    exact mul_div_cancel₀ _ hz


private theorem prod_split {V : Type} [Fintype V] (v : V) (f : V → ℝ) :
    (∏ w, f w) = f v * ∏ w : {w : V // w ≠ v}, f w := by
  exact Fintype.prod_eq_mul_prod_subtype_ne f v

private theorem prod_pair {V : Type} [Fintype V] (r s : V) (hne : r ≠ s)
    (cover : ∀ v, v = r ∨ v = s) (f : V → ℝ) :
    (∏ v, f v) = f r * f s := by
  have h (w : {w : V // w ≠ r}) : w.val = s := (cover w).resolve_left w.property
  letI : Subsingleton {w : V // w ≠ r} := ⟨fun a b => Subtype.ext ((h a).trans (h b).symm)⟩
  rw [prod_split r]
  rw [Fintype.prod_subsingleton (fun w : {w : V // w ≠ r} => f w) ⟨s,Ne.symm hne⟩]

private def orientedProd {V : Type} [Fintype V] (G : SimpleGraph V) (c : V → V → ℝ) : ℝ :=
  by exact ∏ i, ∏ j, if G.Adj i j then c i j else 1

private theorem oriented_prod_leaf {V : Type} [Fintype V] (G : SimpleGraph V)
    (v : V) (u : {w : V // w ≠ v}) (hadj : ∀ w, G.Adj v w ↔ w = u.val)
    (c : V → V → ℝ) :
    orientedProd G c = orientedProd (G.induce {w | w ≠ v}) (fun i j => c i j) *
      c v u * c u v := by
  have hr (w : V) : G.Adj w v ↔ w = u.val := by rw [G.adj_comm]; exact hadj w
  have rowv : (∏ j, if G.Adj v j then c v j else 1) = c v u := by simp [hadj]
  have roww (w : {w : V // w ≠ v}) :
      (∏ j, if G.Adj w.val j then c w j else 1) =
        (if w = u then c w v else 1) *
          ∏ j : {w : V // w ≠ v}, if G.Adj w.val j.val then c w j else 1 := by
    rw [prod_split v]
    congr 1
    simp [hr, Subtype.ext_iff]
  unfold orientedProd
  rw [prod_split v, rowv]
  simp_rw [roww]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  change c v u * (c u v * (∏ i : {w : V // w ≠ v}, ∏ j : {w : V // w ≠ v},
    if G.Adj i.val j.val then c i j else 1)) =
    (∏ i : {w : V // w ≠ v}, ∏ j : {w : V // w ≠ v},
    if G.Adj i.val j.val then c i j else 1) * c v u * c u v
  ring

private theorem oriented_prod_edge {V : Type} [Fintype V] (G : SimpleGraph V)
    (r s : V) (hne : r ≠ s) (cover : ∀ v, v = r ∨ v = s) (hadj : G.Adj r s)
    (c : V → V → ℝ) : orientedProd G c = c r s * c s r := by
  unfold orientedProd
  rw [prod_pair r s hne cover]
  rw [prod_pair r s hne cover, prod_pair r s hne cover]
  simp [hadj, hadj.symm]

/-- Squaring avoids an arbitrary orientation in the symmetric junction-tree density. -/
private def canonicalSquare {V : Type} [Fintype V] {G : SimpleGraph V}
    {X : V → Type} [∀ v, Fintype (X v)] (F : Family G X) (x : ∀ v, X v) : ℝ :=
  (∏ i, F.node i (x i)^2) *
    orientedProd G (fun i j => F.edge i j (x i,x j) / (F.node i (x i) * F.node j (x j)))

private theorem tree_square_positive : ∀ {V : Type} {G : SimpleGraph V} (t : TreeOrder G)
    [Fintype V] (X : V → Type) [∀ v, Fintype (X v)] (F : Family G X) (x : ∀ v, X v),
    (∀ i, F.node i (x i) ≠ 0) → treeMass t F x ^ 2 = canonicalSquare F x := by
  intro V G t
  induction t with
  | @edge V G r s hne cover hadj =>
    intro _ X _ F x hn
    unfold canonicalSquare
    rw [prod_pair r s hne cover, oriented_prod_edge G r s hne cover hadj,
      ← F.edge_swap r s hadj (x r) (x s)]
    change F.edge r s (x r,x s)^2 = _
    field_simp [hn r,hn s]
  | @leaf V G v u hadj old ih =>
    intro _ X _ F x hn
    have huv : G.Adj u.val v := ((hadj u).mpr rfl).symm
    have ho := ih (fun w : {w : V // w ≠ v} => X w) (F.restrict v) (fun w => x w)
      (fun w => hn w)
    change (treeMass old (F.restrict v) (fun w => x w) *
      completedConditional (F.edge u v) (F.node v) (x u) (x v))^2 = _
    rw [mul_pow, ho]
    unfold completedConditional
    rw [F.edge_left u v huv, if_neg (hn u)]
    unfold conditional
    rw [F.edge_left u v huv]
    unfold canonicalSquare
    rw [prod_split v, oriented_prod_leaf G v u hadj,
      F.edge_swap v u ((hadj u).mpr rfl) (x v) (x u)]
    dsimp only [Family.restrict]
    field_simp [hn v,hn u]
    simp only [mul_assoc, mul_comm, mul_left_comm]
    congr!

private theorem tree_square {V : Type} [Fintype V] {G : SimpleGraph V} (t : TreeOrder G)
    (X : V → Type) [∀ v, Fintype (X v)] (F : Family G X) (x : ∀ v, X v) :
    treeMass t F x ^ 2 = canonicalSquare F x := by
  by_cases hn : ∀ i, F.node i (x i) ≠ 0
  · exact tree_square_positive t X F x hn
  · obtain ⟨i,hi⟩ := not_forall.mp hn
    have hz : F.node i (x i) = 0 := not_ne_iff.mp hi
    have hp := tree_law_properties t X F
    have hzero : treeMass t F x = 0 := by
      apply zero_fiber _ (fun y => y i) hp.1 x
      rw [hp.2.2.1 i, hz]
    have hprod : (∏ j, F.node j (x j)^2) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hz]; norm_num)
    simp only [hzero, zero_pow (by decide : 2 ≠ 0), canonicalSquare, hprod, zero_mul]

private theorem tree_order_independence {V : Type} [Fintype V] {G : SimpleGraph V}
    (t t' : TreeOrder G) (X : V → Type) [∀ v, Fintype (X v)] (F : Family G X) :
    treeMass t F = treeMass t' F := by
  funext x
  have h := (tree_square t X F x).trans (tree_square t' X F x).symm
  have hp := (tree_law_properties t X F).1 x
  have hq := (tree_law_properties t' X F).1 x
  nlinarith

/-- A canonical law on every finite graph tree with at least two vertices. -/
def markovLaw {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree)
    (hV : 2 ≤ Fintype.card V) {X : V → Type} [∀ v, Fintype (X v)]
    (F : Family G X) : (∀ v, X v) → ℝ :=
  treeMass (Classical.choose (tree_order_exists G hG hV (Classical.choice hG.connected.nonempty))) F

/-- Actual-law normalization, node and edge marginals, both capped stability bounds,
and independence of all zero-mass conditional rows. -/
theorem actual_tree_stability {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree)
    (hV : 2 ≤ Fintype.card V) (X : V → Type) [∀ v, Fintype (X v)]
    (F H : Family G X) :
    (∀ x, 0 ≤ markovLaw G hG hV F x) ∧ (∑ x, markovLaw G hG hV F x) = 1 ∧
    (∀ x, 0 ≤ markovLaw G hG hV H x) ∧ (∑ x, markovLaw G hG hV H x) = 1 ∧
    (∀ i, pushforward (fun x : ∀ v, X v => x i) (markovLaw G hG hV F) = F.node i) ∧
    (∀ i, pushforward (fun x : ∀ v, X v => x i) (markovLaw G hG hV H) = H.node i) ∧
    (∀ i j, G.Adj i j → pushforward (fun x : ∀ v, X v => (x i,x j))
      (markovLaw G hG hV F) = F.edge i j) ∧
    (∀ i j, G.Adj i j → pushforward (fun x : ∀ v, X v => (x i,x j))
      (markovLaw G hG hV H) = H.edge i j) ∧
    totalVariation (markovLaw G hG hV F) (markovLaw G hG hV H) ≤
      min 1 (edgeBudget F H + nodeBudget G (fun i => totalVariation (F.node i) (H.node i))) ∧
    ((∀ i, F.node i = H.node i) →
      totalVariation (markovLaw G hG hV F) (markovLaw G hG hV H) ≤ min 1 (edgeBudget F H)) ∧
    (∀ root : V, ∃ t : TreeOrder G, t.root = root) ∧
    (∀ (t : TreeOrder G) (K : ∀ i j, X i → X j → ℝ),
      (∀ i j, G.Adj i j → ∀ a b, F.node i a ≠ 0 →
        K i j a b = F.edge i j (a,b) / F.node i a) →
      factorMass t F K = markovLaw G hG hV F) := by
  let t := Classical.choose (tree_order_exists G hG hV (Classical.choice hG.connected.nonempty))
  have hp := tree_law_properties t X F
  have hq := tree_law_properties t X H
  have hb := tree_stability t X F H
  have hc := total_variation_le_one (treeMass t F) (treeMass t H) ⟨hp.1,hp.2.1⟩ ⟨hq.1,hq.2.1⟩
  refine ⟨hp.1,hp.2.1,hq.1,hq.2.1,hp.2.2.1,hq.2.2.1,hp.2.2.2,hq.2.2.2,
    le_min hc hb, ?_, tree_order_exists G hG hV, ?_⟩
  · intro hn
    have hz : nodeBudget G (fun i => totalVariation (F.node i) (H.node i)) = 0 := by
      unfold nodeBudget
      simp [hn, totalVariation]
    rw [hz, add_zero] at hb
    exact le_min hc hb
  · intro t' K hK
    exact (tree_kernel_independence t' X F K (quotient_reconstruction F K hK)).trans
      (tree_order_independence t' t X F)




private def sharpFamily (anti : Bool) : Family (⊤ : SimpleGraph Bool) (fun _ => Bool) where
  node _ _ := 1 / 2
  node_nonnegative _ _ := by norm_num
  node_total _ := by norm_num [Fintype.sum_bool]
  edge _ _ := if anti then antidiagonalLaw else diagonalLaw
  edge_nonnegative _ _ _ := by
    cases anti
    · exact diagonalLaw_nonnegative
    · exact antidiagonalLaw_nonnegative
  edge_left _ _ _ := by
    funext a
    cases anti <;> cases a <;> norm_num [marginal, diagonalLaw, antidiagonalLaw]
  edge_right _ _ _ := by
    intro b
    cases anti <;> cases b <;> norm_num [diagonalLaw, antidiagonalLaw]
  edge_swap _ _ _ := by
    intro a b
    cases anti <;> cases a <;> cases b <;> norm_num [diagonalLaw, antidiagonalLaw]

private theorem bool_tree : (⊤ : SimpleGraph Bool).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨SimpleGraph.connected_top, ?_⟩
  have he : (⊤ : SimpleGraph Bool).edgeFinset = {s(false,true)} := by
    ext e
    induction e using Sym2.ind with
    | _ a b => cases a <;> cases b <;> simp
  have hc : Nat.card (⊤ : SimpleGraph Bool).edgeSet = 1 := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, he]
    simp
  rw [hc, Nat.card_eq_fintype_card]
  decide

/-- The claim that some coefficient strictly below one works for every actual finite tree law. -/
def SmallerEdgeCoefficient : Prop :=
  ∃ c : ℝ, c < 1 ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (hG : G.IsTree)
    (hV : 2 ≤ Fintype.card V) (X : V → Type) [∀ v, Fintype (X v)] (F H : Family G X),
    (∀ i, F.node i = H.node i) →
    totalVariation (markovLaw G hG hV F) (markovLaw G hG hV H) ≤ min 1 (c * edgeBudget F H)

/-- A two-vertex member of the actual universal family excludes every smaller edge coefficient. -/
theorem edge_coefficient_one_sharp : ¬ SmallerEdgeCoefficient := by
  rintro ⟨c,hc,hbound⟩
  let t : TreeOrder (⊤ : SimpleGraph Bool) := .edge false true (by decide)
    (by intro b; cases b <;> simp) (by simp)
  have hV : 2 ≤ Fintype.card Bool := by decide
  have hp : markovLaw (⊤ : SimpleGraph Bool) bool_tree hV (sharpFamily false) =
      treeMass t (sharpFamily false) :=
    tree_order_independence _ t _ _
  have hq : markovLaw (⊤ : SimpleGraph Bool) bool_tree hV (sharpFamily true) =
      treeMass t (sharpFamily true) :=
    tree_order_independence _ t _ _
  have h := hbound Bool ⊤ bool_tree hV (fun _ => Bool) (sharpFamily false) (sharpFamily true)
    (by intro i; rfl)
  rw [hp,hq] at h
  have ht : totalVariation (treeMass t (sharpFamily false)) (treeMass t (sharpFamily true)) = 1 := by
    let e := pairEquiv (X := fun _ : Bool => Bool) false true (by decide)
      (by intro b; cases b <;> simp)
    have he := tv_equiv e diagonalLaw antidiagonalLaw
    change totalVariation (fun x : Bool → Bool => diagonalLaw (e x))
      (fun x => antidiagonalLaw (e x)) = 1
    rw [he, totalVariation]
    norm_num [diagonalLaw, antidiagonalLaw, Fintype.sum_prod_type]
  have hb : edgeBudget (sharpFamily false) (sharpFamily true) = 1 := by
    unfold edgeBudget
    rw [oriented_sum_edge (⊤ : SimpleGraph Bool) false true (by decide)
      (by intro b; cases b <;> simp) (by simp)]
    norm_num [sharpFamily, totalVariation, diagonalLaw, antidiagonalLaw, Fintype.sum_prod_type]
  rw [ht,hb,mul_one] at h
  have hh := h.trans (min_le_right 1 c)
  linarith

#print axioms actual_tree_stability
#print axioms edge_coefficient_one_sharp

end D5.S3.TotalVariation.TreeMarkovStability
