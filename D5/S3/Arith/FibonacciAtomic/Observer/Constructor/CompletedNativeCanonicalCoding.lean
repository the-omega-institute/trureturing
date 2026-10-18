/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/CompletedNativeCanonicalCoding
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Independent atomic expansion and maximal collapse on unrestricted completed trees. -/

import D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.CompletedNativeCanonicalCoding

open NativeCompletionPrefixLifting
open CompletionHomogeneousFixedPoints
open ActualTreeReadoutAcquisition (Address)

/-- All natural-labelled coinductive trees, with no regularity restriction. -/
def codeFunctor : PFunctor.{0,0} where
  A := Nat ⊕ Unit
  B := fun a => match a with
    | .inl _ => Empty
    | .inr _ => Bool

abbrev Code := PFunctor.M codeFunctor

def primitive (n : Nat) : Code := PFunctor.M.mk ⟨.inl n, Empty.elim⟩
def fork (l r : Code) : Code :=
  PFunctor.M.mk ⟨.inr (), fun b : Bool => if b then r else l⟩

def codeOmega : Code :=
  PFunctor.M.corec (fun _ : Unit => (⟨.inr (), fun _ => ()⟩ : codeFunctor Unit)) ()

def codeSubtree : Address → Code → Option Code
  | [], C => some C
  | b :: p, C => match PFunctor.M.dest C with
    | ⟨.inl _, _⟩ => none
    | ⟨.inr _, f⟩ => codeSubtree p (f b)

/-- The atomic collision is excluded at every reached subtree. A leafless
subtree is already the extensional value codeOmega, rather than a retained pair. -/
def Reduced (C : Code) : Prop :=
  ∀ p D, codeSubtree p C = some D → ∀ n, D ≠ fork (primitive (n+1)) (primitive n)

def expansionStep : Code ⊕ CompletionTree → completionFunctor (Code ⊕ CompletionTree)
  | .inr X => PFunctor.map completionFunctor Sum.inr (PFunctor.M.dest X)
  | .inl C => match PFunctor.M.dest C with
    | ⟨.inl n, _⟩ => PFunctor.map completionFunctor Sum.inr (PFunctor.M.dest (atomic n))
    | ⟨.inr _, f⟩ => ⟨.inr (), fun b => .inl (f b)⟩

/-- Total expansion is specified independently of collapse. -/
def expansion (C : Code) : CompletionTree := PFunctor.M.corec expansionStep (.inl C)

noncomputable def collapseStep (X : CompletionTree) : codeFunctor CompletionTree := by
  classical
  exact if h : ∃ n, X = atomic n then ⟨.inl (Classical.choose h), Empty.elim⟩
    else match PFunctor.M.dest X with
    | ⟨.inl b, _⟩ => ⟨.inl (if b then 0 else 1), Empty.elim⟩
    | ⟨.inr _, f⟩ => ⟨.inr (), f⟩

/-- Every encountered atomic subtree is collapsed before descending. -/
noncomputable def collapse (X : CompletionTree) : Code := PFunctor.M.corec collapseStep X

def shift (k : Nat) : Code → Code :=
  PFunctor.M.corec (fun C => match PFunctor.M.dest C with
    | ⟨.inl n, _⟩ => ⟨.inl (n+k), Empty.elim⟩
    | ⟨.inr _, f⟩ => ⟨.inr (), f⟩)

/-- All quantifiers range over the actual unrestricted domains. -/
theorem canonical_coding :
    (∀ X, Reduced (collapse X) ∧ expansion (collapse X) = X) ∧
    (∀ C, Reduced C → collapse (expansion C) = C) ∧
    (Function.Injective collapse ∧ (∀ C, Reduced C → ∃ X, collapse X = C)) ∧
    (∀ k C, Reduced C → Reduced (shift k C)) ∧
    (∀ k X, collapse (rho^[k] X) = shift k (collapse X)) ∧
    (∀ C, Reduced C → (expansion C = Omega ↔ C = codeOmega)) ∧
    (∀ n, collapse (atomic n) = primitive n) ∧
    (∀ l r, (¬ ∃ n, node l r = atomic n) →
      collapse (node l r) = fork (collapse l) (collapse r)) ∧
    (∀ l r, fork l r ≠ codeOmega → ¬ (l = codeOmega ∧ r = codeOmega)) := by
  classical
  have code_cases : ∀ (C : Code), (∃ n, C = primitive n) ∨ ∃ l r, C = fork l r := by
    intro C
    induction C using PFunctor.M.casesOn' with | _ a f =>
    cases a with
    | inl n =>
      left; refine ⟨n, ?_⟩
      congr 2; funext e; exact e.elim
    | inr u =>
      cases u
      right; refine ⟨f false, f true, ?_⟩
      congr 2; funext b; cases b <;> rfl
  have code_inj : ∀ {l r s t : Code}, fork l r = fork s t → l = s ∧ r = t := by
    intro l r s t h
    have hf := (Sigma.mk.inj (PFunctor.M.mk_inj h)).2
    have hf' := eq_of_heq hf
    exact ⟨congrFun hf' false, congrFun hf' true⟩
  have prim_inj : ∀ {n m}, primitive n = primitive m → n = m := by
    intro n m h
    exact Sum.inl.inj (congrArg Sigma.fst (PFunctor.M.mk_inj h))
  have prim_ne_fork : ∀ n l r, primitive n ≠ fork l r := by
    intro n l r h
    have := congrArg Sigma.fst (PFunctor.M.mk_inj h)
    cases this
  have omega_eq : codeOmega = fork codeOmega codeOmega := by
    unfold codeOmega
    conv_lhs => rw [PFunctor.M.corec_def]
    simp only [PFunctor.map, Function.comp_def, fork, ite_self]
    rfl
  have atom_embed : ∀ n, atomic n = embed (GenealogicalFiberTransport.substitution^[n]
      (FreeMagma.of true)) := by
    intro n
    change rho^[n] (embed (FreeMagma.of true)) = _
    exact iterate_embed n _
  have atom_inj : Function.Injective atomic := by
    intro n m h
    apply NativeRankedEqualityCompiler.atomic_injective
    apply NativeCompletionSupportClosure.embed_injective
    simpa only [← atom_embed] using h
  have atom_pair : ∀ n, atomic (n+2) = node (atomic (n+1)) (atomic n) := by
    intro n
    rw [atom_embed, NativeRankedEqualityCompiler.atomic_pair, embed, ← atom_embed, ← atom_embed]
  have leaf_ne_node : ∀ b l r, leaf b ≠ node l r := by
    intro b l r h
    have := congrArg (fun X => (PFunctor.M.dest X).1) h
    simp [leaf, node] at this
  have atom_one : atomic 1 = leaf false := by simp [atomic]
  have atom_ne_omega : ∀ n, atomic n ≠ Omega := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero =>
      intro h
      exact leaf_ne_node true Omega Omega (h.trans omega_node)
    | one =>
      intro h
      rw [atom_one] at h
      exact leaf_ne_node false Omega Omega (h.trans omega_node)
    | more n ih _ =>
      intro h
      rw [atom_pair, omega_node] at h
      exact ih (node_inj h).2
  have copy : ∀ X, PFunctor.M.corec expansionStep (.inr X) = X := by
    intro X0
    apply PFunctor.M.bisim' (fun _ : CompletionTree => True)
      (fun X => PFunctor.M.corec expansionStep (.inr X)) id _ X0 trivial
    intro X _
    let d := PFunctor.M.dest X
    refine ⟨PFunctor.Obj.fst d,
      (fun i => PFunctor.M.corec expansionStep (.inr (PFunctor.Obj.snd d i))),
      PFunctor.Obj.snd d, ?_, (PFunctor.Obj.eta d).symm, ?_⟩
    · rw [PFunctor.M.dest_corec]
      simp only [expansionStep, PFunctor.map, PFunctor.Obj.fst_mk, PFunctor.Obj.snd_mk]
      rfl
    · intro i; exact ⟨PFunctor.Obj.snd d i, trivial, rfl, rfl⟩
  have exp_prim : ∀ n, expansion (primitive n) = atomic n := by
    intro n
    change PFunctor.M.corec expansionStep (.inl (primitive n)) = _
    rw [← copy (atomic n)]
    conv_lhs => rw [PFunctor.M.corec_def]
    conv_rhs => rw [PFunctor.M.corec_def]
    rfl
  have exp_fork : ∀ l r, expansion (fork l r) = node (expansion l) (expansion r) := by
    intro l r
    unfold expansion
    rw [PFunctor.M.corec_def]
    simp only [expansionStep, fork, PFunctor.M.dest_mk, PFunctor.map, node]
    congr 2
    funext b
    cases b <;> rfl
  have col_atom : ∀ n, collapse (atomic n) = primitive n := by
    intro n
    have hn : ∃ m, atomic n = atomic m := ⟨n, rfl⟩
    have hc : Classical.choose hn = n := atom_inj (Classical.choose_spec hn).symm
    unfold collapse
    rw [PFunctor.M.corec_def]
    rw [show collapseStep (atomic n) = ⟨.inl n, Empty.elim⟩ by
      unfold collapseStep
      rw [dif_pos hn, hc]]
    apply congrArg PFunctor.M.mk
    simp only [PFunctor.map]
    congr 1
    funext e
    exact e.elim
  have col_node : ∀ l r, (¬ ∃ n, node l r = atomic n) →
      collapse (node l r) = fork (collapse l) (collapse r) := by
    intro l r h
    unfold collapse
    rw [PFunctor.M.corec_def]
    rw [show collapseStep (node l r) = ⟨.inr (), fun b : Bool => if b then r else l⟩ by
      unfold collapseStep
      rw [dif_neg h]
      rfl]
    simp only [PFunctor.map, fork]
    congr 2
    funext b
    cases b <;> rfl
  have col_primitive : ∀ X n, collapse X = primitive n → X = atomic n := by
    intro X n h
    by_cases ha : ∃ m, X = atomic m
    · obtain ⟨m, rfl⟩ := ha
      rw [col_atom] at h
      exact congrArg atomic (prim_inj h)
    · induction X using tree_cases with
      | leaf_case b =>
        cases b
        · exact (ha ⟨1, atom_one.symm⟩).elim
        · exact (ha ⟨0, rfl⟩).elim
      | node_case l r =>
        rw [col_node l r ha] at h
        exact (prim_ne_fork n _ _ h.symm).elim
  have root_reduced : ∀ X n, collapse X ≠ fork (primitive (n+1)) (primitive n) := by
    intro X n h
    by_cases ha : ∃ m, X = atomic m
    · obtain ⟨m, rfl⟩ := ha
      rw [col_atom] at h
      exact prim_ne_fork m _ _ h
    · induction X using tree_cases with
      | leaf_case b =>
        cases b
        · exact ha ⟨1, atom_one.symm⟩
        · exact ha ⟨0, rfl⟩
      | node_case l r =>
        rw [col_node l r ha] at h
        obtain ⟨hl, hr⟩ := code_inj h
        exact ha ⟨n+2, by rw [col_primitive l _ hl, col_primitive r _ hr, atom_pair]⟩
  have col_reduced : ∀ X, Reduced (collapse X) := by
    intro X p
    induction p generalizing X with
    | nil =>
      intro D hd n
      have : collapse X = D := Option.some.inj hd
      rw [← this]
      exact root_reduced X n
    | cons b p ih =>
      intro D hd n
      by_cases ha : ∃ m, X = atomic m
      · obtain ⟨m, rfl⟩ := ha
        rw [col_atom] at hd
        simp [codeSubtree, primitive] at hd
      · induction X using tree_cases with
        | leaf_case c =>
          cases c
          · exact (ha ⟨1, atom_one.symm⟩).elim
          · exact (ha ⟨0, rfl⟩).elim
        | node_case l r =>
          rw [col_node l r ha] at hd
          cases b
          · exact ih l D hd n
          · exact ih r D hd n
  have red_children : ∀ l r, Reduced (fork l r) → Reduced l ∧ Reduced r := by
    intro l r h
    exact ⟨fun p D hd n => h (false :: p) D hd n,
      fun p D hd n => h (true :: p) D hd n⟩
  have exp_atomic : ∀ n C, Reduced C → expansion C = atomic n → C = primitive n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro C hc he
      obtain (⟨m, rfl⟩ | ⟨l, r, rfl⟩) := code_cases C
      · rw [exp_prim] at he
        exact congrArg primitive (atom_inj he)
      · rw [exp_fork] at he
        cases n with
        | zero => exact (leaf_ne_node true _ _ he.symm).elim
        | succ n =>
          cases n with
          | zero =>
            rw [atom_one] at he
            exact (leaf_ne_node false _ _ he.symm).elim
          | succ n =>
            rw [atom_pair] at he
            obtain ⟨hl, hr⟩ := node_inj he
            obtain ⟨hcl, hcr⟩ := red_children l r hc
            have el := ih (n+1) (by omega) l hcl hl
            have er := ih n (by omega) r hcr hr
            exact (hc [] _ rfl n (by rw [el, er])).elim
  have left_inverse : ∀ X, expansion (collapse X) = X := by
    intro X
    apply readout_ext
    intro p
    induction p generalizing X with
    | nil =>
      by_cases ha : ∃ n, X = atomic n
      · obtain ⟨n, rfl⟩ := ha
        rw [col_atom, exp_prim]
      · induction X using tree_cases with
        | leaf_case b =>
          cases b
          · exact (ha ⟨1, atom_one.symm⟩).elim
          · exact (ha ⟨0, rfl⟩).elim
        | node_case l r => rw [col_node l r ha, exp_fork]; rfl
    | cons b p ih =>
      by_cases ha : ∃ n, X = atomic n
      · obtain ⟨n, rfl⟩ := ha
        rw [col_atom, exp_prim]
      · induction X using tree_cases with
        | leaf_case c =>
          cases c
          · exact (ha ⟨1, atom_one.symm⟩).elim
          · exact (ha ⟨0, rfl⟩).elim
        | node_case l r =>
          rw [col_node l r ha, exp_fork]
          cases b
          · exact ih l
          · exact ih r
  have right_inverse : ∀ C, Reduced C → collapse (expansion C) = C := by
    apply PFunctor.M.bisim' Reduced (fun C => collapse (expansion C)) id
    intro C hc
    obtain (⟨n, rfl⟩ | ⟨l, r, rfl⟩) := code_cases C
    · refine ⟨.inl n, Empty.elim, Empty.elim, ?_, by simp [primitive, PFunctor.Obj.mk], fun e => e.elim⟩
      rw [exp_prim, col_atom]; simp [primitive, PFunctor.Obj.mk]
    · have ha : ¬ ∃ n, node (expansion l) (expansion r) = atomic n := by
        rintro ⟨n, hn⟩
        have h := exp_atomic n (fork l r) hc (by rw [exp_fork]; exact hn)
        exact prim_ne_fork n l r h.symm
      obtain ⟨hl, hr⟩ := red_children l r hc
      refine ⟨.inr (), (fun b : Bool => if b then collapse (expansion r) else collapse (expansion l)),
        (fun b : Bool => if b then r else l), ?_, by simp [fork, PFunctor.Obj.mk], ?_⟩
      · rw [exp_fork, col_node _ _ ha]; simp [fork, PFunctor.Obj.mk]
      · intro b; cases b
        · exact ⟨l, hl, rfl, rfl⟩
        · exact ⟨r, hr, rfl, rfl⟩
  have shift_prim : ∀ k n, shift k (primitive n) = primitive (n+k) := by
    intro k n
    unfold shift
    rw [PFunctor.M.corec_def]
    simp only [primitive, PFunctor.M.dest_mk, PFunctor.map]
    apply congrArg PFunctor.M.mk
    congr 1
    funext e
    exact e.elim
  have shift_fork : ∀ k l r, shift k (fork l r) = fork (shift k l) (shift k r) := by
    intro k l r
    unfold shift
    rw [PFunctor.M.corec_def]
    simp only [fork, PFunctor.M.dest_mk, PFunctor.map]
    congr 2
    funext b
    cases b <;> rfl
  have rho_not_alpha : ∀ X, rho X ≠ leaf true := by
    intro X
    induction X using tree_cases with
    | leaf_case b =>
      cases b
      · rw [rho_beta]; exact Ne.symm (leaf_ne_node _ _ _)
      · rw [rho_alpha]
        intro h
        have hh := congrArg (fun Y => (PFunctor.M.dest Y).1) h
        simp only [leaf, PFunctor.M.dest_mk] at hh
        exact Bool.false_ne_true (Sum.inl.inj hh)
    | node_case l r => rw [rho_node]; exact Ne.symm (leaf_ne_node _ _ _)
  have rho_atomic_reflect : ∀ X, (∃ n, rho X = atomic n) → ∃ n, X = atomic n := by
    intro X ⟨n, hn⟩
    cases n with
    | zero => exact (rho_not_alpha X hn).elim
    | succ n =>
      refine ⟨n, rho_injective ?_⟩
      exact hn.trans (Function.iterate_succ_apply' rho n (leaf true))
  have iterate_atomic_reflect : ∀ k X, (∃ n, rho^[k] X = atomic n) → ∃ n, X = atomic n := by
    intro k
    induction k with
    | zero => intro X h; exact h
    | succ k ih =>
      intro X h
      apply ih X
      apply rho_atomic_reflect
      simpa only [Function.iterate_succ_apply'] using h
  have atom_shift : ∀ k n, rho^[k] (atomic n) = atomic (n+k) := by
    intro k n
    exact (Function.iterate_add_apply rho k n (leaf true)).symm.trans
      (by rw [Nat.add_comm]; rfl)
  have shift_intertwine : ∀ k X, collapse (rho^[k] X) = shift k (collapse X) := by
    intro k0 X0
    apply PFunctor.M.bisim' (fun _ : Nat × CompletionTree => True)
      (fun q => collapse (rho^[q.1] q.2)) (fun q => shift q.1 (collapse q.2)) _ ⟨k0, X0⟩ trivial
    rintro ⟨k, X⟩ _
    by_cases ha : ∃ n, X = atomic n
    · obtain ⟨n, rfl⟩ := ha
      refine ⟨.inl (n+k), Empty.elim, Empty.elim, ?_, ?_, fun e => e.elim⟩
      · rw [atom_shift, col_atom]; simp [primitive, PFunctor.Obj.mk]
      · rw [col_atom, shift_prim]; simp [primitive, PFunctor.Obj.mk]
    · induction X using tree_cases with
      | leaf_case b =>
        cases b
        · exact (ha ⟨1, atom_one.symm⟩).elim
        · exact (ha ⟨0, rfl⟩).elim
      | node_case l r =>
        have hn : ¬ ∃ n, node (rho^[k] l) (rho^[k] r) = atomic n := by
          intro hh
          apply ha
          apply iterate_atomic_reflect k (node l r)
          simpa only [iterate_node] using hh
        refine ⟨.inr (), (fun b : Bool => if b then collapse (rho^[k] r) else collapse (rho^[k] l)),
          (fun b : Bool => if b then shift k (collapse r) else shift k (collapse l)), ?_, ?_, ?_⟩
        · rw [iterate_node, col_node _ _ hn]; simp [fork, PFunctor.Obj.mk]
        · rw [col_node _ _ ha, shift_fork]; simp [fork, PFunctor.Obj.mk]
        · intro b; cases b
          · exact ⟨⟨k, l⟩, trivial, rfl, rfl⟩
          · exact ⟨⟨k, r⟩, trivial, rfl, rfl⟩
  have col_omega : collapse Omega = codeOmega := by
    have hn : ¬ ∃ n, node Omega Omega = atomic n := by
      rintro ⟨n, hn⟩
      exact atom_ne_omega n (hn.symm.trans omega_node.symm)
    apply PFunctor.M.bisim' (fun _ : Unit => True)
      (fun _ => collapse Omega) (fun _ => codeOmega) _ () trivial
    intro _ _
    refine ⟨.inr (), (fun _ => collapse Omega), (fun _ => codeOmega), ?_, ?_, ?_⟩
    · conv_lhs => rw [omega_node, col_node _ _ hn]
      simp only [fork, PFunctor.M.dest_mk, ite_self]
      rfl
    · conv_lhs => rw [omega_eq]
      simp only [fork, PFunctor.M.dest_mk, ite_self]
      rfl
    · intro _; exact ⟨(), trivial, rfl, rfl⟩
  refine ⟨fun X => ⟨col_reduced X, left_inverse X⟩, right_inverse, ?_, ?_,
    shift_intertwine, ?_, col_atom, col_node, ?_⟩
  · refine ⟨?_, fun C hc => ⟨expansion C, right_inverse C hc⟩⟩
    intro X Y h
    exact (left_inverse X).symm.trans ((congrArg expansion h).trans (left_inverse Y))
  · intro k C hc
    rw [← right_inverse C hc, ← shift_intertwine]
    exact col_reduced _
  · intro C hc
    constructor
    · intro h
      rw [← right_inverse C hc, h, col_omega]
    · intro h
      rw [h, ← col_omega, left_inverse]
  · intro l r h ⟨hl, hr⟩
    apply h
    rw [hl, hr, ← omega_eq]

#print axioms canonical_coding

end D5.S3.Arith.FibonacciAtomic.Observer.CompletedNativeCanonicalCoding
