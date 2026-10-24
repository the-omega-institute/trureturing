/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalNativeConstruction
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual simultaneous native solutions of original functional cases with arbitrary free choices. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.OriginalFunctionalNormalization
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.OriginalFiniteResolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.OriginalNativeConstruction

open GenealogicalFiberTransport (Source substitution)
open NativeCompletionPrefixLifting
open CompletionHomogeneousFixedPoints
open OriginalFunctionalNormalization

variable {k m : Nat}

private theorem power_add (a b : Nat) (e : Expr k m) :
    power a (power b e) = power (a+b) e := by
  induction e with
  | ground t => simp only [power, Function.iterate_add_apply]
  | token j c => simp only [power]; congr 1; omega
  | omega => rfl
  | var c i => simp only [power]; congr 1; omega
  | pair e f ihe ihf => simp only [power, ihe, ihf]

private abbrev State (k m : Nat) := Expr k m ⊕ CompletionTree

private def copyHead (X : CompletionTree) : completionFunctor (State k m) :=
  completionFunctor.map Sum.inr (PFunctor.M.dest X)

private def head (mode : Fin k → Bool) (p : Fin k → Nat)
    (g : Fin m → CompletionTree) : Expr k m → completionFunctor (State k m)
  | .ground t => copyHead (embed t)
  | .token j c => copyHead (if mode j then atomic (p j+c) else Omega)
  | .omega => copyHead Omega
  | .var a i => copyHead (rho^[a] (g i))
  | .pair e f => ⟨.inr (), fun b : Bool => .inl (if b then f else e)⟩

/-- Only a defining root is unfolded. A pair produces native children immediately;
fixed powers are distributed using the actual native substitution. -/
private def step (E : Definitions k m) (mode : Fin k → Bool) (p : Fin k → Nat)
    (g : Fin m → CompletionTree) : State k m → completionFunctor (State k m)
  | .inr X => copyHead X
  | .inl (.var a i) => match E i with
    | none => head mode p g (.var a i)
    | some e => head mode p g (power a e)
  | .inl e => head mode p g e

private def run (E : Definitions k m) (mode : Fin k → Bool) (p : Fin k → Nat)
    (g : Fin m → CompletionTree) : State k m → CompletionTree :=
  PFunctor.M.corec (step E mode p g)

/-- The constructed native state vector, before restoring root-link coordinates. -/
def native (E : Definitions k m) (mode : Fin k → Bool) (p : Fin k → Nat)
    (g : Fin m → CompletionTree) (i : Fin m) : CompletionTree :=
  run E mode p g (.inl (.var 0 i))

private theorem run_copy (E : Definitions k m) (mode : Fin k → Bool) (p : Fin k → Nat)
    (g : Fin m → CompletionTree) (X : CompletionTree) : run E mode p g (.inr X) = X := by
  have h : ∀ Y, PFunctor.M.dest (run E mode p g (.inr Y)) =
      completionFunctor.map (fun Z => run E mode p g (.inr Z)) (PFunctor.M.dest Y) := by
    intro Y
    rw [run, PFunctor.M.dest_corec]
    rfl
  have one := PFunctor.M.corec_unique (fun Y : CompletionTree => PFunctor.M.dest Y)
    (fun Y => run E mode p g (.inr Y)) h
  have two := PFunctor.M.corec_unique (fun Y : CompletionTree => PFunctor.M.dest Y)
    id (fun _ => by simp [PFunctor.id_map])
  exact congrFun (one.trans two.symm) X

private theorem run_head (E : Definitions k m) (mode : Fin k → Bool) (p : Fin k → Nat)
    (g : Fin m → CompletionTree) (e : Expr k m) :
    PFunctor.M.mk (completionFunctor.map (run E mode p g) (head mode p g e)) =
      match e with
      | .ground t => embed t
      | .token j c => if mode j then atomic (p j+c) else Omega
      | .omega => Omega
      | .var a i => rho^[a] (g i)
      | .pair l r => node (run E mode p g (.inl l)) (run E mode p g (.inl r)) := by
  have copy : ∀ X : CompletionTree,
      PFunctor.M.mk (completionFunctor.map (run E mode p g) (copyHead X)) = X := by
    intro X
    have eq : completionFunctor.map (run E mode p g) (copyHead X) = PFunctor.M.dest X := by
      change completionFunctor.map (fun Y => run E mode p g (.inr Y))
        (PFunctor.M.dest X) = PFunctor.M.dest X
      have hf : (fun Y => run E mode p g (.inr Y)) = id :=
        funext (run_copy E mode p g)
      rw [hf, PFunctor.id_map]
    rw [eq, PFunctor.M.mk_dest]
  cases e <;> simp only [head, copy]
  apply congrArg PFunctor.M.mk
  apply Sigma.ext rfl
  apply heq_of_eq
  funext b
  cases b <;> rfl

private theorem run_ground (E : Definitions k m) (mode : Fin k → Bool) (p : Fin k → Nat)
    (g : Fin m → CompletionTree) (t : Source) : run E mode p g (.inl (.ground t)) = embed t := by
  rw [run, PFunctor.M.corec_def]
  exact run_head E mode p g (.ground t)

private theorem run_token (E : Definitions k m) (mode : Fin k → Bool) (p : Fin k → Nat)
    (g : Fin m → CompletionTree) (j : Fin k) (c : Nat) :
    run E mode p g (.inl (.token j c)) = if mode j then atomic (p j+c) else Omega := by
  rw [run, PFunctor.M.corec_def]
  exact run_head E mode p g (.token j c)

private theorem run_omega (E : Definitions k m) (mode : Fin k → Bool) (p : Fin k → Nat)
    (g : Fin m → CompletionTree) : run E mode p g (.inl .omega) = Omega := by
  rw [run, PFunctor.M.corec_def]
  exact run_head E mode p g .omega

private theorem run_pair (E : Definitions k m) (mode : Fin k → Bool) (p : Fin k → Nat)
    (g : Fin m → CompletionTree) (l r : Expr k m) :
    run E mode p g (.inl (.pair l r)) =
      node (run E mode p g (.inl l)) (run E mode p g (.inl r)) := by
  rw [run, PFunctor.M.corec_def]
  exact run_head E mode p g (.pair l r)

private theorem run_var (E : Definitions k m) (mode : Fin k → Bool) (p : Fin k → Nat)
    (g : Fin m → CompletionTree) (a : Nat) (i : Fin m) :
    run E mode p g (.inl (.var a i)) =
      match E i with
      | none => rho^[a] (g i)
      | some e => PFunctor.M.mk (completionFunctor.map (run E mode p g)
          (head mode p g (power a e))) := by
  conv_lhs => rw [run, PFunctor.M.corec_def]
  cases he : E i with
  | none => simpa only [step, he] using run_head E mode p g (.var a i)
  | some e => simp only [step, he]; rfl

private theorem run_power (E : Definitions k m) (guarded : PairGuarded E)
    (mode : Fin k → Bool) (p : Fin k → Nat) (g : Fin m → CompletionTree)
    (a : Nat) (e : Expr k m) :
    run E mode p g (.inl (power a e)) = rho^[a] (run E mode p g (.inl e)) := by
  let C := run E mode p g
  let Rel := fun X Y : CompletionTree => X = Y ∨
    ∃ a e, X = C (.inl (power a e)) ∧ Y = rho^[a] (C (.inl e))
  have diag : ∀ X Y, X = Y → ∃ s f f',
      PFunctor.M.dest X = ⟨s, f⟩ ∧ PFunctor.M.dest Y = ⟨s, f'⟩ ∧
        ∀ b, Rel (f b) (f' b) := by
    intro X Y eq
    subst Y
    cases hd : PFunctor.M.dest X with
    | mk s f => exact ⟨s, f, f, rfl, rfl, fun _ => Or.inl rfl⟩
  apply PFunctor.M.bisim Rel ?_ _ _ (Or.inr ⟨a, e, rfl, rfl⟩)
  intro X Y h
  rcases h with eq | ⟨a, e, rfl, rfl⟩
  · exact diag X Y eq
  · cases e with
    | ground t =>
        apply diag
        exact (run_ground E mode p g _).trans ((iterate_embed a t).symm.trans
          (congrArg (rho^[a]) (run_ground E mode p g t).symm))
    | token j c =>
        apply diag
        change run E mode p g (.inl (.token j (a+c))) = _
        simp only [C, run_token]
        by_cases hm : mode j = true
        · simp only [hm, ↓reduceIte, atomic]
          rw [← Function.iterate_add_apply]
          exact congrArg (fun n => rho^[n] (leaf true)) (by omega)
        · simp [hm, iterate_omega]
    | omega =>
        apply diag
        simp only [power, C, run_omega, iterate_omega]
    | pair l r =>
        refine ⟨.inr (), (fun b : Bool => if b then C (.inl (power a r)) else C (.inl (power a l))),
          (fun b : Bool => if b then rho^[a] (C (.inl r)) else rho^[a] (C (.inl l))), ?_, ?_, ?_⟩
        · simp only [power, C, run_pair, node, PFunctor.M.dest_mk]; rfl
        · change PFunctor.M.dest (rho^[a] (run E mode p g (.inl (.pair l r)))) = _
          rw [run_pair, iterate_node]
          simp only [node, PFunctor.M.dest_mk]
          rfl
        · intro b; cases b
          · exact Or.inr ⟨a, l, rfl, rfl⟩
          · exact Or.inr ⟨a, r, rfl, rfl⟩
    | var b i =>
        cases he : E i with
        | none =>
            apply diag
            simp only [power, C, run_var, he]
            exact Function.iterate_add_apply rho a b (g i)
        | some f =>
            cases f with
            | var c j => exact (guarded i c j he).elim
            | ground t =>
                apply diag
                simp only [power, C, run_var, he, run_head]
                simp only [iterate_embed, ← Function.iterate_add_apply]
            | token j c =>
                apply diag
                simp only [power, C, run_var, he, run_head]
                by_cases hm : mode j = true
                · simp only [hm, ↓reduceIte, atomic]
                  rw [← Function.iterate_add_apply]
                  exact congrArg (fun n => rho^[n] (leaf true)) (by omega)
                · simp [hm, iterate_omega]
            | omega =>
                apply diag
                simp only [power, C, run_var, he, run_head, iterate_omega]
            | pair l r =>
                refine ⟨.inr (),
                  (fun t : Bool => if t then C (.inl (power (a+b) r)) else C (.inl (power (a+b) l))),
                  (fun t : Bool => if t then rho^[a] (C (.inl (power b r))) else rho^[a] (C (.inl (power b l)))),
                  ?_, ?_, ?_⟩
                · simp only [power, C, run_var, he, run_head, node, PFunctor.M.dest_mk]; rfl
                · simp only [C, run_var, he, power, run_head]
                  rw [iterate_node]
                  simp only [node, PFunctor.M.dest_mk]
                  rfl
                · intro t; cases t
                  · exact Or.inr ⟨a, power b l, by rw [power_add], rfl⟩
                  · exact Or.inr ⟨a, power b r, by rw [power_add], rfl⟩

private theorem run_value (E : Definitions k m) (guarded : PairGuarded E)
    (mode : Fin k → Bool) (p : Fin k → Nat) (g : Fin m → CompletionTree) (e : Expr k m) :
    run E mode p g (.inl e) = value mode p (native E mode p g) e := by
  induction e with
  | ground t => exact run_ground E mode p g t
  | token j c => exact run_token E mode p g j c
  | omega => exact run_omega E mode p g
  | var a i =>
      have h := run_power E guarded mode p g a (.var 0 i)
      simpa only [power, Nat.add_zero, value, native] using h
  | pair l r ihl ihr => simp only [run_pair, value, ihl, ihr]

private theorem native_solution (E : Definitions k m) (guarded : PairGuarded E)
    (mode : Fin k → Bool) (p : Fin k → Nat) (g : Fin m → CompletionTree) :
    Solution E mode p (native E mode p g) ∧
      ∀ i, E i = none → native E mode p g i = g i := by
  constructor
  · intro i e he
    rw [← run_value E guarded mode p g e]
    unfold native
    rw [run_var, he]
    cases e with
    | var a j => exact (guarded i a j he).elim
    | ground t => simpa only [power, Function.iterate_zero_apply, run_head] using (run_ground E mode p g t).symm
    | token j c => simpa only [power, Nat.zero_add, run_head] using (run_token E mode p g j c).symm
    | omega => simpa only [power, run_head] using (run_omega E mode p g).symm
    | pair l r =>
        rw [run_head]
        have h := run_power E guarded mode p g 0 (.pair l r)
        simpa only [power, run_pair, Function.iterate_zero_apply] using congrArg (fun X => X) h
  · intro i he
    simp only [native, run_var, he, Function.iterate_zero_apply]

private theorem native_unique (E : Definitions k m) (guarded : PairGuarded E)
    (mode : Fin k → Bool) (p : Fin k → Nat) (g v : Fin m → CompletionTree)
    (hv : Solution E mode p v) (free : ∀ i, E i = none → v i = g i) :
    v = native E mode p g := by
  let interp : State k m → CompletionTree := Sum.elim (value mode p v) id
  have copy : ∀ X, completionFunctor.map interp (copyHead X) = PFunctor.M.dest X := by
    intro X
    rfl
  have head_eq : ∀ e : Expr k m, (∀ a i, e ≠ .var a i) →
      PFunctor.M.dest (value mode p v e) = completionFunctor.map interp (head mode p g e) := by
    intro e h
    cases e with
    | var a i => exact (h a i rfl).elim
    | ground t => exact (copy (embed t)).symm
    | token j c => exact (copy _).symm
    | omega => exact (copy Omega).symm
    | pair l r =>
        simp only [value, head, node, PFunctor.M.dest_mk, PFunctor.map]
        apply Sigma.ext rfl
        apply heq_of_eq
        funext b
        cases b <;> rfl
  have morph : ∀ x, PFunctor.M.dest (interp x) =
      completionFunctor.map interp (step E mode p g x) := by
    intro x
    cases x with
    | inr X => exact (copy X).symm
    | inl e =>
        cases e with
        | ground t => exact (copy (embed t)).symm
        | token j c => exact (copy _).symm
        | omega => exact (copy Omega).symm
        | pair l r => exact head_eq (.pair l r) (by intros; intro h; cases h)
        | var a i =>
            change PFunctor.M.dest (rho^[a] (v i)) = _
            cases he : E i with
            | none => simp only [step, he, head, free i he]; exact (copy _).symm
            | some f =>
                rw [hv i f he, ← value_power]
                simp only [step, he]
                change PFunctor.M.dest (value mode p v (power a f)) =
                  completionFunctor.map interp (head mode p g (power a f))
                apply head_eq
                intro b j eq
                cases f <;> simp [power] at eq
                exact (guarded i _ _ he).elim
  have unique := PFunctor.M.corec_unique (step E mode p g) interp morph
  funext i
  exact congrFun unique (.inl (.var 0 i))

/-- The extra internal slot is fixed divergent data, never an original parameter. -/
def encode : Expr k m → CompletionPositiveDriftRegion.Expr (k+1) m
  | .ground t => .ground t
  | .token j c => .token j.succ c
  | .omega => .token 0 0
  | .var a i => .var a i
  | .pair l r => .pair (encode l) (encode r)

def encodeDefinitions (E : Definitions k m) : OriginalFiniteResolution.Definitions (k+1) m :=
  fun i => (E i).map encode

private theorem encode_value (mode : Fin k → Bool) (p : Fin k → Nat)
    (v : Fin m → CompletionTree) (e : Expr k m) :
    CompletionPositiveDriftRegion.value (Fin.cases false mode) (Fin.cases 0 p) v (encode e) =
      value mode p v e := by
  induction e with
  | ground t => rfl
  | token j c => simp [encode, CompletionPositiveDriftRegion.value, value]
  | omega => simp [encode, CompletionPositiveDriftRegion.value, value]
  | var a i => rfl
  | pair l r ihl ihr => exact congrArg₂ node ihl ihr

private theorem encode_solution (E : Definitions k m) (mode : Fin k → Bool)
    (p : Fin k → Nat) (v : Fin m → CompletionTree) (hv : Solution E mode p v) :
    OriginalFiniteResolution.Solution (encodeDefinitions E) (Fin.cases false mode)
      (Fin.cases 0 p) v := by
  intro i f hf
  cases he : E i with
  | none => simp [encodeDefinitions, he] at hf
  | some e =>
      have ef : encode e = f := by simpa [encodeDefinitions, he] using hf
      subst f
      rw [encode_value]
      exact hv i e he

/-- Internal finite expressions use only original parameter names after decoding. -/
def decodeFinite : OriginalFiniteResolution.FiniteExpr (k+1) →
    OriginalFiniteResolution.FiniteExpr k
  | .ground t => .ground t
  | .token j c => Fin.cases (.ground (substitution^[c] (.of true)))
      (fun i => .token i c) j
  | .power a e => .power a (decodeFinite e)
  | .pair l r => .pair (decodeFinite l) (decodeFinite r)

private theorem decode_finite_value (p : Fin k → Nat)
    (f : OriginalFiniteResolution.FiniteExpr (k+1)) :
    OriginalFiniteResolution.finiteValue p (decodeFinite f) =
      OriginalFiniteResolution.finiteValue (Fin.cases 0 p) f := by
  induction f with
  | ground t => rfl
  | token j c =>
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [decodeFinite, OriginalFiniteResolution.finiteValue]
      · simp [decodeFinite, OriginalFiniteResolution.finiteValue]
  | power a e ih => simp only [decodeFinite, OriginalFiniteResolution.finiteValue, ih]
  | pair l r ihl ihr => simp only [decodeFinite, OriginalFiniteResolution.finiteValue, ihl, ihr]

/-- The original-state-count finite compiler is reused on the exact internal encoding. -/
def finiteCompile (E : Definitions k m) (mode : Fin k → Bool) (e : Expr k m) :
    Option (OriginalFiniteResolution.FiniteExpr k) :=
  (OriginalFiniteResolution.compile (encodeDefinitions E) (Fin.cases false mode) (encode e)).map
    decodeFinite

private theorem finite_compile_sound (E : Definitions k m) (mode : Fin k → Bool)
    (e : Expr k m) (f : OriginalFiniteResolution.FiniteExpr k) (hf : finiteCompile E mode e = some f)
    (p : Fin k → Nat) (v : Fin m → CompletionTree) (hv : Solution E mode p v) :
    value mode p v e = embed (OriginalFiniteResolution.finiteValue p f) := by
  cases hc : OriginalFiniteResolution.compile (encodeDefinitions E) (Fin.cases false mode)
      (encode e) with
  | none => simp [finiteCompile, hc] at hf
  | some g =>
      have gf : decodeFinite g = f := by simpa [finiteCompile, hc] using hf
      subst f
      rw [decode_finite_value, ← encode_value mode p v e]
      exact (OriginalFiniteResolution.original_finite_resolution (k+1) m
        (encodeDefinitions E) (Fin.cases false mode)).2 (encode e) g hc
          (Fin.cases 0 p) v (encode_solution E mode p v hv)

/-- Every original functional case has an actual native completed solution. The
normalization is chosen from syntax alone. Arbitrary normalized free values give
solutions; every original solution is recovered with its own free values. -/
theorem original_native_construction (E : Definitions k m) :
    ∃ (N : Definitions k m) (R : Fin m → Expr k m), PairGuarded N ∧
      ∀ (mode : Fin k → Bool) (p : Fin k → Nat),
        (∀ g : Fin m → CompletionTree,
          Solution E mode p (reconstruct mode p R (native N mode p g))) ∧
        (∀ v : Fin m → CompletionTree, Solution E mode p v →
          Solution N mode p v ∧ reconstruct mode p R v = v ∧
            reconstruct mode p R (native N mode p v) = v) ∧
        (∀ g u : Fin m → CompletionTree, Solution N mode p u →
          (∀ i, N i = none → u i = g i) → u = native N mode p g) ∧
        (∀ g : Fin m → CompletionTree,
          Solution N mode p (native N mode p g) ∧
            ∀ i, N i = none → native N mode p g i = g i) ∧
        (∀ (e : Expr k m) (f : OriginalFiniteResolution.FiniteExpr k),
          finiteCompile E mode e = some f → ∀ v : Fin m → CompletionTree,
            Solution E mode p v → value mode p v e =
              embed (OriginalFiniteResolution.finiteValue p f)) := by
  obtain ⟨N, R, guarded, sound, restrict⟩ := root_link_normalization E
  refine ⟨N, R, guarded, ?_⟩
  intro mode p
  refine ⟨?_, ?_, ?_, native_solution N guarded mode p, ?_⟩
  · intro g
    exact sound mode p _ (native_solution N guarded mode p g).1
  · intro v hv
    obtain ⟨hn, hr⟩ := restrict mode p v hv
    refine ⟨hn, hr, ?_⟩
    have eq := native_unique N guarded mode p v v hn (by intros; rfl)
    rw [← eq, hr]
  · intro g u hu hf
    exact native_unique N guarded mode p g u hu hf
  · intro e f hf v hv
    exact finite_compile_sound E mode e f hf p v hv

#print axioms original_native_construction

end D5.S3.Arith.FibonacciAtomic.Observer.OriginalNativeConstruction
