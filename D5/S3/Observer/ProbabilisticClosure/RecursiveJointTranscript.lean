/- GID: D5/S3/Observer/ProbabilisticClosure/RecursiveJointTranscript
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/RecursiveJointTranscript
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recursive typed joint residuals preserve complete ordered adaptive transcript laws. -/

import D5.S3.ConceptDynamics.RefinementFactorization.RealizedImageKernelFactorization
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Typed source rows and their finite adaptive acquired-history laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.RecursiveJointTranscript

open D5.S3.ConceptDynamics.RefinementFactorization.RealizedImageKernelFactorization

universe u

/-- Action values include their parameters and permission requirements. Each
terminal belongs to its action's typed interface, disjoint from successful states. -/
structure Interface where
  Ty : Type u
  State : Ty → Type u
  Observation : Ty → Type u
  Action : Ty → Ty → Type u
  Event : {i j : Ty} → Action i j → Type u
  Record : {i j : Ty} → Action i j → Type u
  Terminal : {i j : Ty} → Action i j → Type u

abbrev Output (T : Interface.{u}) {i j : T.Ty} (a : T.Action i j) :=
  T.Event a × (T.State j ⊕ T.Terminal a) × T.Record a

/-- The source supplies legal rows and the complete normalized refusal triple.
Fields affecting future legality or responses belong to the source or records. -/
structure Source (T : Interface.{u}) where
  observe : {i : T.Ty} → T.State i → T.Observation i
  legal : {i j : T.Ty} → (a : T.Action i j) → T.State i → Prop
  kernel : {i j : T.Ty} → (a : T.Action i j) → (z : T.State i) →
    legal a z → PMF (Output T a)
  refusal : {i j : T.Ty} → (a : T.Action i j) → (z : T.State i) →
    ¬ legal a z → T.Event a × T.Terminal a × T.Record a

open Classical in
def Source.total {T : Interface.{u}} (S : Source T) {i j : T.Ty}
    (a : T.Action i j) (z : T.State i) : PMF (Output T a) :=
  if h : S.legal a z then S.kernel a z h else
    PMF.pure ((S.refusal a z h).1, Sum.inr (S.refusal a z h).2.1, (S.refusal a z h).2.2)

/-- Only successful successors are quotiented; every event, record and terminal
is retained exactly. The realized image changes no output equality. -/
def jointView {T : Interface.{u}} (R : (i : T.Ty) → Setoid (T.State i))
    {i j : T.Ty} (a : T.Action i j) (x : Output T a) :
    T.Event a × (Quotient (R j) ⊕ T.Terminal a) × T.Record a :=
  (x.1, Sum.map (Quotient.mk (R j)) id x.2.1, x.2.2)

/-- The actual closed joint recursion starts at the current observation kernel
and retains the preceding relation at every refinement. -/
def residual {T : Interface.{u}} (S : Source T) :
    ℕ → (i : T.Ty) → Setoid (T.State i)
  | 0, _ => Setoid.ker S.observe
  | n + 1, i => residual S n i ⊓ Setoid.ker (fun z =>
      fun a : (j : T.Ty) × T.Action i j =>
        (S.legal a.2 z,
          (S.total a.2 z).map (Set.rangeFactorization (jointView (residual S n) a.2))))

/-- The ordered acquired alphabet contains observations, selected parameterized
actions, joint events and records, and distinct stop, horizon and terminal tags. -/
inductive Token (T : Interface.{u}) where
  | observed (i : T.Ty) (o : T.Observation i)
  | chosen {i j : T.Ty} (a : T.Action i j)
  | event {i j : T.Ty} (a : T.Action i j) (e : T.Event a)
  | recorded {i j : T.Ty} (a : T.Action i j) (r : T.Record a)
  | terminal {i j : T.Ty} (a : T.Action i j) (f : T.Terminal a)
  | stopped (i : T.Ty)
  | horizon (i : T.Ty)

/-- Selectors and archive updates receive only declared acquired data. Permission
checks may use the full acquired prefix and archive; source legality is separate.
Randomized stopping is the `none` decision. -/
structure Policy (T : Interface.{u}) (Archive : Type u) where
  write : Archive → List (Token T) → List (Token T) → Archive
  permitted : (i : T.Ty) → T.Observation i → Archive → List (Token T) →
    ((j : T.Ty) × T.Action i j) → Prop
  select : ℕ → (i : T.Ty) → T.Observation i → Archive → List (Token T) →
    PMF (Option ((j : T.Ty) × T.Action i j))
  selects_permitted : ∀ n i o c h a, some a ∈ (select n i o c h).support →
    permitted i o c h a

abbrev Transcript (T : Interface.{u}) (Archive : Type u) :=
  List (Token T) × List Archive

/-- Consume one complete source output, writing its event and record before
continuing, or retaining the source's fixed terminal without continuation. -/
def respond {T : Interface.{u}} {Archive : Type u} (P : Policy T Archive)
    {i j : T.Ty} (next : T.State j → Archive → List (Token T) → PMF (Transcript T Archive))
    (a : T.Action i j) (c : Archive) (h : List (Token T))
    (x : Output T a) : PMF (Transcript T Archive) :=
  let block := [Token.event a x.1, Token.recorded a x.2.2]
  let c' := P.write c h block
  let h' := h ++ block
  match x.2.1 with
  | .inl z => (next z c' h').map fun out => (out.1, c :: out.2)
  | .inr f => PMF.pure (h' ++ [Token.terminal a f],
      [c, c', P.write c' h' [Token.terminal a f]])

/-- Executed laws are constructed from source rows, never supplied as a law table.
The result retains the entire ordered acquired history jointly with the initial
archive and each chronological archive update. -/
def run {T : Interface.{u}} (S : Source T) {Archive : Type u} (P : Policy T Archive) :
    ℕ → (i : T.Ty) → T.State i → Archive → List (Token T) → PMF (Transcript T Archive)
  | 0, i, z, c, h =>
      let obs := [Token.observed i (S.observe z)]
      let c' := P.write c h obs
      PMF.pure (h ++ obs ++ [Token.horizon i], [c, c', P.write c' (h ++ obs) [Token.horizon i]])
  | n + 1, i, z, c, h =>
      let o := S.observe z
      let h' := h ++ [Token.observed i o]
      let c' := P.write c h [Token.observed i o]
      (P.select n i o c' h').bind fun decision =>
        match decision with
        | none => PMF.pure (h' ++ [Token.stopped i], [c, c', P.write c' h' [Token.stopped i]])
        | some ⟨j, a⟩ =>
            ((S.total a z).bind (respond P (run S P n j) a
              (P.write c' h' [Token.chosen a]) (h' ++ [Token.chosen a]))).map
                fun out => (out.1, [c, c'] ++ out.2)

private theorem residual_observe {T : Interface.{u}} (S : Source T) (n : ℕ)
    {i : T.Ty} {z w : T.State i} (h : residual S n i z w) :
    S.observe z = S.observe w := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih h.1

/-- At every smaller finite depth, the recursively generated joint residual
preserves the complete ordered law of every acquired-history-only policy on
matching archives. No continuation-law invariance is assumed. -/
theorem recursive_residual_preserves_adaptive_law {T : Interface.{u}} (S : Source T)
    (Archive : Type u) (n : ℕ) {i : T.Ty} {z w : T.State i}
    (related : residual S n i z w) :
    ∀ d ≤ n, ∀ (P : Policy T Archive) (c : Archive) (h : List (Token T)),
      run S P d i z c h = run S P d i w c h := by
  induction n generalizing i with
  | zero =>
      intro d hd P c h
      have hd' : d = 0 := Nat.eq_zero_of_le_zero hd
      subst d
      simp only [run, residual_observe S 0 related]
  | succ n ih =>
      intro d hd P c h
      have ho := residual_observe S (n + 1) related
      cases d with
      | zero => simp only [run, ho]
      | succ d =>
          have hd' : d ≤ n := Nat.le_of_succ_le_succ hd
          simp only [run, ho]
          congr 1
          funext decision
          cases decision with
          | none => rfl
          | some a =>
              obtain ⟨j, a⟩ := a
              let c' := P.write (P.write c h [Token.observed i (S.observe w)])
                (h ++ [Token.observed i (S.observe w)]) [Token.chosen a]
              let h' := (h ++ [Token.observed i (S.observe w)]) ++ [Token.chosen a]
              let f := respond P (run S P d j) a c' h'
              let q := jointView (residual S n) a
              apply congrArg (PMF.map _)
              change (S.total a z).bind f = (S.total a w).bind f
              have hfiber : Setoid.ker q ≤ Setoid.ker f := by
                intro x y hxy
                rcases x with ⟨e, x, r⟩
                rcases y with ⟨e', y, r'⟩
                change (e, Sum.map (Quotient.mk (residual S n j)) id x, r) =
                  (e', Sum.map (Quotient.mk (residual S n j)) id y, r') at hxy
                obtain ⟨he, hpair⟩ := Prod.mk.inj hxy
                obtain ⟨hnext, hr⟩ := Prod.mk.inj hpair
                subst e'
                subst r'
                cases x with
                | inl x =>
                    cases y with
                    | inl y =>
                        exact congrArg (PMF.map _) (ih (Quotient.exact (Sum.inl.inj hnext)) d hd' P _ _)
                    | inr y => cases hnext
                | inr x =>
                    cases y with
                    | inl y => cases hnext
                    | inr y =>
                        have ht : x = y := Sum.inr.inj hnext
                        subst y
                        rfl
              obtain ⟨factor, factor_eq, _⟩ :=
                (realized_image_unique_factorization_iff_reverse_kernel f q).mpr hfiber
              let g : Set.range q → PMF (Transcript T Archive) := fun v => (factor v).val
              have hf : f = g ∘ Set.rangeFactorization q := by
                funext x
                exact congrArg Subtype.val (congrFun factor_eq x)
              have rows := congrFun related.2 ⟨j, a⟩
              have rows' : (S.total a z).map (Set.rangeFactorization q) =
                  (S.total a w).map (Set.rangeFactorization q) := congrArg Prod.snd rows
              rw [hf, ← PMF.bind_map, ← PMF.bind_map, rows']

#print axioms recursive_residual_preserves_adaptive_law

end D5.S3.Observer.ProbabilisticClosure.RecursiveJointTranscript
