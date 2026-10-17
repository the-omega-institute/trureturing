/- GID: D5/S3/Arith/FibonacciAtomic/Observer/CompletionHomogeneousFixedPoints
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Homogeneous native feedback on finite and infinite completed trees. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionSupportClosure
import D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedEqualityCompiler

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply)
open NativeCompletionPrefixLifting

/-- A reached original subtree; descendants of leaves have no subtree. -/
def subtree : Address → CompletionTree → Option CompletionTree
  | [], X => some X
  | b :: p, X => match PFunctor.M.dest X with
    | ⟨.inl _, _⟩ => none
    | ⟨.inr _, f⟩ => subtree p (f b)

def originalReach (X : CompletionTree) (p : Address) : Prop :=
  ∃ Y, subtree p X = some Y

private def rhoStep : CompletionTree ⊕ Bool → completionFunctor (CompletionTree ⊕ Bool)
  | .inr b => ⟨.inl b, Empty.elim⟩
  | .inl X => match PFunctor.M.dest X with
    | ⟨.inl true, _⟩ => ⟨.inl false, Empty.elim⟩
    | ⟨.inl false, _⟩ => ⟨.inr (), fun b => .inr b⟩
    | ⟨.inr _, f⟩ => ⟨.inr (), fun b => .inl (f b)⟩

/-- The native substitution acts on leaves and preserves every original branch. -/
def rho (X : CompletionTree) : CompletionTree :=
  PFunctor.M.corec rhoStep (.inl X)

private theorem corec_leaf (b : Bool) : PFunctor.M.corec rhoStep (.inr b) = leaf b := by
  rw [PFunctor.M.corec_def]
  apply congrArg PFunctor.M.mk
  apply Sigma.ext (by simp [rhoStep, PFunctor.map, PFunctor.Obj.mk, PFunctor.Obj.fst, PFunctor.Obj.snd])
  apply heq_of_eq
  funext e
  exact e.elim

@[simp] theorem rho_alpha : rho (leaf true) = leaf false := by
  unfold rho
  rw [PFunctor.M.corec_def]
  apply congrArg PFunctor.M.mk
  apply Sigma.ext (by simp [rhoStep, leaf, PFunctor.map, PFunctor.Obj.mk, PFunctor.Obj.fst, PFunctor.Obj.snd])
  apply heq_of_eq
  funext e
  exact e.elim

@[simp] theorem rho_beta : rho (leaf false) = node (leaf false) (leaf true) := by
  unfold rho
  rw [PFunctor.M.corec_def]
  simp only [rhoStep, leaf, node, PFunctor.M.dest_mk, PFunctor.map]
  congr 1
  congr 1
  funext b
  cases b <;> exact corec_leaf _

@[simp] theorem rho_node (l r : CompletionTree) :
    rho (node l r) = node (rho l) (rho r) := by
  unfold rho
  rw [PFunctor.M.corec_def]
  simp only [rhoStep, node, PFunctor.M.dest_mk, PFunctor.map]
  congr 1
  congr 1
  funext b
  cases b <;> rfl

theorem node_inj {l r s t : CompletionTree} (h : node l r = node s t) :
    l = s ∧ r = t := by
  have h' := PFunctor.M.mk_inj h
  have hf : (fun b : Bool => if b then r else l) =
      (fun b : Bool => if b then t else s) := by
    exact eq_of_heq (Sigma.mk.inj h').2
  exact ⟨congrFun hf false, congrFun hf true⟩

private theorem leaf_ne_node (b : Bool) (l r : CompletionTree) : leaf b ≠ node l r := by
  intro h
  have hh := congrArg (fun X => (PFunctor.M.dest X).1) h
  simp [leaf, node] at hh

private theorem leaf_inj {b c : Bool} (h : leaf b = leaf c) : b = c := by
  have hh := congrArg (fun X => (PFunctor.M.dest X).1) h
  exact Sum.inl.inj (by simpa only [leaf, PFunctor.M.dest_mk] using hh)

/-- Equality is determined by all original replies, including absent addresses. -/
theorem readout_ext {X Y : CompletionTree}
    (h : ∀ p, completionReadout p X = completionReadout p Y) : X = Y := by
  apply PFunctor.M.bisim (fun X Y => ∀ p, completionReadout p X = completionReadout p Y) _ X Y h
  intro S T same
  induction S using tree_cases with
  | leaf_case b =>
    induction T using tree_cases with
    | leaf_case c =>
      have root := same []
      have bc : b = c := by cases b <;> cases c <;> simp_all [completionReadout, leaf]
      subst c
      exact ⟨.inl b, Empty.elim, Empty.elim, by simp [leaf, PFunctor.Obj.mk], by simp [leaf, PFunctor.Obj.mk], fun i => i.elim⟩
    | node_case l r =>
      have root := same []
      cases b <;> simp [completionReadout, leaf, node] at root
  | node_case l r =>
    induction T using tree_cases with
    | leaf_case b =>
      have root := same []
      cases b <;> simp [completionReadout, leaf, node] at root
    | node_case s t =>
      refine ⟨.inr (), (fun b : Bool => if b then r else l),
        (fun b : Bool => if b then t else s), by simp [node, PFunctor.Obj.mk], by simp [node, PFunctor.Obj.mk], ?_⟩
      intro b p
      exact same (b :: p)

private theorem rho_ne_alpha (X : CompletionTree) : rho X ≠ leaf true := by
  induction X using tree_cases with
  | leaf_case b =>
    cases b
    · rw [rho_beta]; exact (leaf_ne_node _ _ _).symm
    · rw [rho_alpha]; intro h; have := leaf_inj h; contradiction
  | node_case l r => rw [rho_node]; exact (leaf_ne_node _ _ _).symm

/-- Native substitution remains injective on unrestricted completed trees. -/
theorem rho_injective : Function.Injective rho := by
  intro X Y eq
  apply readout_ext
  intro p
  induction p generalizing X Y with
  | nil =>
    induction X using tree_cases with
    | leaf_case b =>
      induction Y using tree_cases with
      | leaf_case c => cases b <;> cases c <;> simp_all [leaf_ne_node, Ne.symm (leaf_ne_node _ _ _)]
      | node_case l r =>
        cases b
        · rw [rho_beta, rho_node] at eq
          exact False.elim (rho_ne_alpha r (node_inj eq).2.symm)
        · rw [rho_alpha, rho_node] at eq
          exact False.elim (leaf_ne_node _ _ _ eq)
    | node_case l r =>
      induction Y using tree_cases with
      | leaf_case b =>
        cases b
        · rw [rho_node, rho_beta] at eq
          exact False.elim (rho_ne_alpha r (node_inj eq).2)
        · rw [rho_node, rho_alpha] at eq
          exact False.elim (leaf_ne_node _ _ _ eq.symm)
      | node_case s t => rfl
  | cons b p ih =>
    induction X using tree_cases with
    | leaf_case c =>
      induction Y using tree_cases with
      | leaf_case d => simp [completionReadout, leaf]
      | node_case l r =>
        cases c
        · rw [rho_beta, rho_node] at eq
          exact False.elim (rho_ne_alpha r (node_inj eq).2.symm)
        · rw [rho_alpha, rho_node] at eq
          exact False.elim (leaf_ne_node _ _ _ eq)
    | node_case l r =>
      induction Y using tree_cases with
      | leaf_case c =>
        cases c
        · rw [rho_node, rho_beta] at eq
          exact False.elim (rho_ne_alpha r (node_inj eq).2)
        · rw [rho_node, rho_alpha] at eq
          exact False.elim (leaf_ne_node _ _ _ eq.symm)
      | node_case s t =>
        rw [rho_node, rho_node] at eq
        obtain ⟨hl, hr⟩ := node_inj eq
        cases b <;> simp only [completionReadout, node, PFunctor.M.dest_mk]
        · exact ih hl
        · exact ih hr

@[simp] theorem rho_embed (t : Source) : rho (embed t) = embed (substitution t) := by
  induction t with
  | of b => cases b <;> simp [embed, substitution]
  | mul s t ihs iht => simpa [embed, substitution] using congrArg₂ node ihs iht

@[simp] theorem iterate_embed (n : Nat) (t : Source) :
    rho^[n] (embed t) = embed (substitution^[n] t) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, rho_embed, Function.iterate_succ_apply']

@[simp] theorem iterate_node (n : Nat) (l r : CompletionTree) :
    rho^[n] (node l r) = node (rho^[n] l) (rho^[n] r) :=
  Function.Semiconj₂.iterate rho_node n l r


/-- Finiteness refers to the exact existing finite-source embedding. -/
def IsFinite (X : CompletionTree) : Prop := ∃ t : Source, embed t = X

private theorem finite_leaf (b : Bool) : IsFinite (leaf b) := ⟨.of b, rfl⟩

theorem finite_subtree (p : Address) {X Y : CompletionTree}
    (finite : IsFinite X) (present : subtree p X = some Y) : IsFinite Y := by
  obtain ⟨t, rfl⟩ := finite
  induction p generalizing t with
  | nil => exact ⟨t, Option.some.inj present⟩
  | cons b p ih =>
    cases t with
    | of c => simp [embed, subtree, leaf] at present
    | mul l r =>
      cases b
      · exact ih (t := l) present
      · exact ih (t := r) present

private theorem finite_rho_iff (X : CompletionTree) : IsFinite (rho X) ↔ IsFinite X := by
  constructor
  · rintro ⟨t, ht⟩
    induction t generalizing X with
    | of b =>
      induction X using tree_cases with
      | leaf_case c => exact finite_leaf c
      | node_case l r =>
        exact False.elim (leaf_ne_node b (rho l) (rho r) (by simpa [embed] using ht))
    | mul s t ihs iht =>
      induction X using tree_cases with
      | leaf_case b => exact finite_leaf b
      | node_case l r =>
        have eq := node_inj (show node (embed s) (embed t) = node (rho l) (rho r) by
          simpa [embed] using ht)
        obtain ⟨s', hs⟩ := ihs l eq.1
        obtain ⟨t', ht'⟩ := iht r eq.2
        exact ⟨.mul s' t', by simp [embed, hs, ht']⟩
  · rintro ⟨t, rfl⟩
    exact ⟨substitution t, (rho_embed t).symm⟩

theorem finite_iterate_iff (n : Nat) (X : CompletionTree) :
    IsFinite (rho^[n] X) ↔ IsFinite X := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', finite_rho_iff, ih]

/-- Native evolution transports precisely the originally reached subtree. -/
theorem original_subtree_transport (n : Nat) (p : Address) (X Y : CompletionTree)
    (present : subtree p X = some Y) : subtree p (rho^[n] X) = some (rho^[n] Y) := by
  induction p generalizing X with
  | nil => simpa [subtree] using congrArg (Option.map (rho^[n])) present
  | cons b p ih =>
    induction X using tree_cases with
    | leaf_case c => simp [subtree, leaf] at present
    | node_case l r =>
      rw [iterate_node]
      cases b
      · exact ih l present
      · exact ih r present

/-- An infinite image subtree cannot be born below an original finite leaf. -/
theorem infinite_subtree_origin (n : Nat) (p : Address) (X Z : CompletionTree)
    (present : subtree p (rho^[n] X) = some Z) (infinite : ¬ IsFinite Z) :
    ∃ Y, subtree p X = some Y ∧ rho^[n] Y = Z ∧ ¬ IsFinite Y := by
  have reached : ∃ Y, subtree p X = some Y := by
    induction p generalizing X with
    | nil => exact ⟨X, rfl⟩
    | cons b p ih =>
      induction X using tree_cases with
      | leaf_case c =>
        exact False.elim (infinite (finite_subtree (b :: p)
          ((finite_iterate_iff n _).mpr (finite_leaf c)) present))
      | node_case l r =>
        rw [iterate_node] at present
        cases b
        · exact ih l present
        · exact ih r present
  obtain ⟨Y, hY⟩ := reached
  have transport : rho^[n] Y = Z :=
    Option.some.inj ((original_subtree_transport n p X Y hY).symm.trans present)
  exact ⟨Y, hY, transport,
    fun h => infinite (transport ▸ (finite_iterate_iff n Y).mpr h)⟩

/-- A finite pair expression whose leaves are powers of one shared residual. -/
abbrev Homogeneous := FreeMagma Nat

def eval (H : Homogeneous) (X : CompletionTree) : CompletionTree :=
  match H with
  | .of b => rho^[b] X
  | .mul A B => node (eval A X) (eval B X)

/-- A concrete frontier occurrence retains its address and exponent. -/
inductive Occurs : Homogeneous → Address → Nat → Prop
  | atom (b : Nat) : Occurs (.of b) [] b
  | left {A B p b} : Occurs A p b → Occurs (.mul A B) (false :: p) b
  | right {A B p b} : Occurs B p b → Occurs (.mul A B) (true :: p) b

private theorem eval_occurs {H : Homogeneous} {p : Address} {b : Nat}
    (occ : Occurs H p b) (X : CompletionTree) :
    subtree p (eval H X) = some (rho^[b] X) := by
  induction occ with
  | atom b => rfl
  | left _ ih => exact ih
  | right _ ih => exact ih

private theorem eval_iterate (H : Homogeneous) (n : Nat) (X : CompletionTree) :
    eval H (rho^[n] X) = rho^[n] (eval H X) := by
  induction H with
  | of b => exact Function.Commute.iterate_iterate_self rho b n X
  | mul A B ihA ihB => simp only [eval, iterate_node, ihA, ihB]

/-- The preimage is the actual original subtree and solves the same feedback equation. -/
theorem infinite_feedback_descent (a : Nat) (H : Homogeneous) (p : Address) (b : Nat)
    (occ : Occurs H p b) (lt : b < a) (X : CompletionTree)
    (infinite : ¬ IsFinite X) (feedback : rho^[a] X = eval H X) :
    ∃ Y, originalReach X p ∧ subtree p X = some Y ∧ ¬ IsFinite Y ∧
      X = rho^[a-b] Y ∧ rho^[a] Y = eval H Y := by
  have present : subtree p (rho^[a] X) = some (rho^[b] X) := by
    rw [feedback]; exact eval_occurs occ X
  obtain ⟨Y, original, transport, infY⟩ := infinite_subtree_origin a p X _ present
    (fun h => infinite ((finite_iterate_iff b X).mp h))
  have back : X = rho^[a-b] Y := by
    apply (rho_injective.iterate b)
    rw [← Function.iterate_add_apply, Nat.add_sub_of_le (Nat.le_of_lt lt)]
    exact transport.symm
  have stable : rho^[a] Y = eval H Y := by
    apply (rho_injective.iterate (a-b))
    rw [← eval_iterate, ← back]
    rw [Function.Commute.iterate_iterate_self rho (a-b) a Y, ← back]
    exact feedback
  exact ⟨Y, ⟨Y, original⟩, original, infY, back, stable⟩

/-- Repeated descent uses one fixed frontier occurrence and preserves the entire equation. -/
theorem infinite_feedback_preimages (a : Nat) (H : Homogeneous) (p : Address) (b : Nat)
    (occ : Occurs H p b) (lt : b < a) (X : CompletionTree)
    (infinite : ¬ IsFinite X) (feedback : rho^[a] X = eval H X) (k : Nat) :
    ∃ Y, ¬ IsFinite Y ∧ X = rho^[k * (a-b)] Y ∧ rho^[a] Y = eval H Y := by
  induction k with
  | zero => exact ⟨X, infinite, by simp, feedback⟩
  | succ k ih =>
    obtain ⟨Y, infY, back, stable⟩ := ih
    obtain ⟨Z, _, _, infZ, yz, stableZ⟩ :=
      infinite_feedback_descent a H p b occ lt Y infY stable
    refine ⟨Z, infZ, ?_, stableZ⟩
    rw [back, yz, ← Function.iterate_add_apply, Nat.succ_mul]

/-- The unique tree with no leaves. -/
def Omega : CompletionTree :=
  PFunctor.M.corec (fun _ : Unit => (⟨.inr (), fun _ => ()⟩ : completionFunctor Unit)) ()

theorem omega_node : Omega = node Omega Omega := by
  unfold Omega
  conv_lhs => rw [PFunctor.M.corec_def]
  simp only [PFunctor.map, Function.comp_def, node, ite_self]
  rfl

/-- Every reply strictly above depth n is a branch. -/
def Full (n : Nat) (X : CompletionTree) : Prop :=
  ∀ p : Address, p.length < n → completionReadout p X = .branch

private theorem full_zero (X : CompletionTree) : Full 0 X := by
  intro p h; omega

private theorem full_node (n : Nat) (l r : CompletionTree) :
    Full (n+1) (node l r) ↔ Full n l ∧ Full n r := by
  constructor
  · intro h
    exact ⟨fun p hp => h (false :: p) (by simpa using hp),
      fun p hp => h (true :: p) (by simpa using hp)⟩
  · rintro ⟨hl, hr⟩ p hp
    cases p with
    | nil => simp [completionReadout, node]
    | cons b p =>
      have hp' : p.length < n := by simpa using hp
      cases b
      · exact hl p hp'
      · exact hr p hp'

private theorem full_leaf_false (n : Nat) (b : Bool) : ¬ Full (n+1) (leaf b) := by
  intro h
  have root := h [] (by simp)
  cases b <;> simp [completionReadout, leaf] at root

private theorem full_rho (n : Nat) (X : CompletionTree) (h : Full n X) : Full n (rho X) := by
  induction n generalizing X with
  | zero => exact full_zero _
  | succ n ih =>
    induction X using tree_cases with
    | leaf_case b => exact False.elim (full_leaf_false n b h)
    | node_case l r =>
      obtain ⟨hl, hr⟩ := (full_node n l r).mp h
      rw [rho_node]
      exact (full_node n _ _).mpr ⟨ih l hl, ih r hr⟩

private theorem full_iterate (n k : Nat) (X : CompletionTree) (h : Full n X) :
    Full n (rho^[k] X) := by
  induction k with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply']; exact full_rho n _ ih

private theorem two_steps_deepen (n : Nat) (X : CompletionTree) (h : Full n X) :
    Full (n+1) (rho (rho X)) := by
  induction n generalizing X with
  | zero =>
    induction X using tree_cases with
    | leaf_case b =>
      cases b <;> simp only [rho_alpha, rho_beta, rho_node]
      · exact (full_node 0 _ _).mpr ⟨full_zero _, full_zero _⟩
      · exact (full_node 0 _ _).mpr ⟨full_zero _, full_zero _⟩
    | node_case l r =>
      simp only [rho_node]
      exact (full_node 0 _ _).mpr ⟨full_zero _, full_zero _⟩
  | succ n ih =>
    induction X using tree_cases with
    | leaf_case b => exact False.elim (full_leaf_false n b h)
    | node_case l r =>
      obtain ⟨hl, hr⟩ := (full_node n l r).mp h
      simp only [rho_node]
      exact (full_node (n+1) _ _).mpr ⟨ih l hl, ih r hr⟩

theorem iterate_full (n : Nat) (X : CompletionTree) : Full n (rho^[2*n] X) := by
  induction n with
  | zero => exact full_zero _
  | succ n ih =>
    rw [show 2*(n+1) = 2+2*n by omega, Function.iterate_add_apply]
    exact two_steps_deepen n _ ih

private theorem omega_readout (p : Address) : completionReadout p Omega = .branch := by
  induction p with
  | nil => rw [omega_node]; simp [completionReadout, node]
  | cons b p ih =>
    rw [omega_node]
    cases b <;> simpa [completionReadout, node] using ih

theorem eq_omega_of_full (X : CompletionTree) (h : ∀ n, Full n X) : X = Omega := by
  apply readout_ext
  intro p
  rw [h (p.length+1) p (by omega), omega_readout]

@[simp] theorem rho_omega : rho Omega = Omega := by
  apply eq_omega_of_full
  intro n
  exact full_rho n Omega (fun p _ => omega_readout p)

theorem iterate_omega (n : Nat) : rho^[n] Omega = Omega := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, rho_omega]

private theorem eval_omega (H : Homogeneous) : eval H Omega = Omega := by
  induction H with
  | of b => exact iterate_omega b
  | mul A B ihA ihB => simpa only [eval, ihA, ihB] using omega_node.symm

private theorem full_eval (H : Homogeneous) (n : Nat) (X : CompletionTree)
    (h : Full n X) : Full n (eval H X) := by
  induction H with
  | of b => exact full_iterate n b X h
  | mul A B ihA ihB =>
    intro p hp
    exact ((full_node n _ _).mpr ⟨ihA, ihB⟩) p (by omega)

private def subtract (a : Nat) : Homogeneous → Homogeneous
  | .of b => .of (b-a)
  | .mul A B => .mul (subtract a A) (subtract a B)

private theorem eval_subtract (a : Nat) (H : Homogeneous)
    (lower : ∀ p b, Occurs H p b → a ≤ b) (X : CompletionTree) :
    eval H X = rho^[a] (eval (subtract a H) X) := by
  induction H with
  | of b =>
    have hb := lower [] b (.atom b)
    simp only [eval, subtract, ← Function.iterate_add_apply, Nat.add_sub_of_le hb]
  | mul A B ihA ihB =>
    simp only [eval, subtract, iterate_node]
    rw [ihA (fun p b hp => lower (false :: p) b (.left hp)),
      ihB (fun p b hp => lower (true :: p) b (.right hp))]

private theorem guarded_feedback_omega (a : Nat) (A B : Homogeneous) (X : CompletionTree)
    (lower : ∀ p b, Occurs (.mul A B) p b → a ≤ b)
    (feedback : rho^[a] X = eval (.mul A B) X) : X = Omega := by
  have fixed : X = eval (subtract a (.mul A B)) X :=
    (rho_injective.iterate a) (feedback.trans (eval_subtract a _ lower X))
  apply eq_omega_of_full
  intro n
  induction n with
  | zero => exact full_zero X
  | succ n ih =>
    rw [fixed]
    exact (full_node n _ _).mpr
      ⟨full_eval _ n X ih, full_eval _ n X ih⟩

/-- Every infinite homogeneous feedback solution is the leafless completed tree. -/
theorem infinite_feedback_omega (a : Nat) (A B : Homogeneous) (X : CompletionTree)
    (infinite : ¬ IsFinite X) (feedback : rho^[a] X = eval (.mul A B) X) : X = Omega := by
  classical
  by_cases lower : ∀ p b, Occurs (.mul A B) p b → a ≤ b
  · exact guarded_feedback_omega a A B X lower feedback
  · push Not at lower
    obtain ⟨p, b, occ, lt⟩ := lower
    apply eq_omega_of_full
    intro n
    obtain ⟨Y, _, back, _⟩ :=
      infinite_feedback_preimages a (.mul A B) p b occ lt X infinite feedback (2*n)
    have bound : 2*n ≤ 2*n*(a-b) := Nat.le_mul_of_pos_right _ (by omega)
    rw [back, show 2*n*(a-b) = 2*n + (2*n*(a-b)-2*n) by omega,
      Function.iterate_add_apply]
    exact iterate_full n _


private def finiteEval (H : Homogeneous) (t : Source) : Source :=
  match H with
  | .of b => substitution^[b] t
  | .mul A B => .mul (finiteEval A t) (finiteEval B t)

private theorem eval_embed (H : Homogeneous) (t : Source) :
    eval H (embed t) = embed (finiteEval H t) := by
  induction H with
  | of b => exact iterate_embed b t
  | mul A B ihA ihB => simpa only [eval, finiteEval, embed] using congrArg₂ node ihA ihB

open NativePrefixIdentityReflection (gamma gamma_iterate gamma_pair gamma_parent
  atomicRank gamma_positive)

private theorem mass_eval_ge (H : Homogeneous) (t : Source) :
    gamma t ≤ gamma (finiteEval H t) := by
  induction H with
  | of b => simp [finiteEval, gamma_iterate]
  | mul A B ihA _ => exact ihA.trans (gamma_parent _ _).1

theorem atomicRank_sound (t : Source) (c : Nat) (h : atomicRank t = some c) :
    substitution^[c] (.of true) = t := by
  induction t generalizing c with
  | of b =>
    cases b
    · have hc : c = 1 := by simpa [atomicRank] using h.symm
      subst c; rfl
    · have hc : c = 0 := by simpa [atomicRank] using h.symm
      subst c; rfl
  | mul s t ihs iht =>
    cases hs : atomicRank s with
    | none => simp [atomicRank, hs] at h
    | some m =>
      cases ht : atomicRank t with
      | none => simp [atomicRank, hs, ht] at h
      | some n =>
        by_cases mn : m = n+1
        · have hc : c = n+2 := by simpa [atomicRank, hs, ht, mn] using h.symm
          subst c
          rw [NativeRankedEqualityCompiler.atomic_pair, ← mn, ihs m hs, iht n ht]
        · simp [atomicRank, hs, ht, mn] at h

private theorem finite_feedback_atomic (a : Nat) (A B : Homogeneous) (t : Source)
    (feedback : rho^[a] (embed t) = eval (.mul A B) (embed t)) :
    ∃ c : Nat, embed t = rho^[c] (leaf true) := by
  have eq : substitution^[a] t = finiteEval (.mul A B) t :=
    NativeCompletionSupportClosure.embed_injective (by
      simpa only [iterate_embed, eval_embed] using feedback)
  have zero : gamma t = 0 := by
    by_contra nz
    have ha := mass_eval_ge A t
    have hb := mass_eval_ge B t
    have masses := congrArg gamma eq
    simp only [gamma_iterate, finiteEval] at masses
    rw [gamma_pair _ _ (Or.inl (by omega))] at masses
    omega
  cases hc : atomicRank t with
  | none => have := (gamma_positive t).mpr hc; omega
  | some c =>
    refine ⟨c, ?_⟩
    have ht := atomicRank_sound t c hc
    rw [show leaf true = embed (.of true) by rfl, iterate_embed, ht]

/-- The finite native orbit, embedded in the unrestricted completion. -/
def atomic (c : Nat) : CompletionTree := rho^[c] (leaf true)

/-- The syntax has a pair at its root; it contains no ground or second residual. -/
def PairRoot (H : Homogeneous) : Prop := ∃ A B, H = .mul A B

/-- The complete solution set: the leafless tree and, exactly when the alpha test
holds, every finite atomic iterate. No finiteness condition is imposed on X. -/
theorem completed_homogeneous_split (a : Nat) (H : Homogeneous) (root : PairRoot H)
    (X : CompletionTree) :
    rho^[a] X = eval H X ↔
      X = Omega ∨ (eval H (leaf true) = atomic a ∧ ∃ c : Nat, X = atomic c) := by
  obtain ⟨A, B, rfl⟩ := root
  constructor
  · intro feedback
    classical
    by_cases finite : IsFinite X
    · obtain ⟨t, rfl⟩ := finite
      obtain ⟨c, hc⟩ := finite_feedback_atomic a A B t feedback
      refine Or.inr ⟨?_, c, hc⟩
      rw [hc, eval_iterate, Function.Commute.iterate_iterate_self rho a c] at feedback
      exact ((rho_injective.iterate c) feedback).symm
    · exact Or.inl (infinite_feedback_omega a A B X finite feedback)
  · rintro (rfl | ⟨test, c, rfl⟩)
    · rw [iterate_omega, eval_omega]
    · change rho^[a] (rho^[c] (leaf true)) = eval (.mul A B) (rho^[c] (leaf true))
      rw [eval_iterate, test]
      exact Function.Commute.iterate_iterate_self rho a c _

end D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints
