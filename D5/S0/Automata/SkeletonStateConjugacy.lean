/- GID: D5/S0/Automata/SkeletonStateConjugacy
   generality: G
   mirror-B: D5/B/S0/Automata/SkeletonStateConjugacy
   mirror-E: none(waiver:explicit-recurrent-renaming)
   anchors: []
   utility: none
   digest: An explicit recurrent-state equivalence preserves every partial skeleton evaluation and its exact canonical signature cost, justifying finite zero-map covers. -/

import D5.S0.Automata.BinaryZeckendorfBlockSkeleton

/- The existing Skeleton, SignatureFiber, CanonicalState and evalFrom own the
   mathematical objects. This is recurrent-carrier transport, complementary to
   SkeletonSlotProfileSymmetry's renaming of slots on one fixed Skeleton.
   The finite coverage program supplies explicit permutations, so its use does
   not require treating canonical-labeling correctness as a new axiom.
   Logical proof review is distinct from unperformed Lean elaboration here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.SkeletonStateConjugacy

open D5.S0.Automata.BinaryZeckendorfBlockSkeleton

universe u v w
variable {Output : Type u} {State : Type v} {Target : Type w}

/-- Reindex the recurrent carrier and the return coordinate of each signature. -/
def reindex (K : Skeleton Output State) (e : State ≃ Target) :
    Skeleton Output Target where
  start := e K.start
  zeroStep := fun q => (K.zeroStep (e.symm q)).map e
  oneSignature := fun q => (K.oneSignature (e.symm q)).map
    (fun signature => (signature.1, signature.2.map e))
  zeroOutput := fun q => K.zeroOutput (e.symm q)

/-- Every continuation, including failed partial runs, is preserved. -/
theorem evalFrom_reindex (K : Skeleton Output State) (e : State ≃ Target)
    (q : State) (blocks : List ReturnBlock) (terminal : TerminalChannel) :
    (reindex K e).evalFrom (e q) blocks terminal =
      K.evalFrom q blocks terminal := by
  induction blocks generalizing q with
  | nil =>
      cases terminal <;>
        simp [Skeleton.evalFrom, reindex, Option.map_map, Function.comp_def]
  | cons block blocks ih =>
      cases block with
      | zero =>
          cases hz : K.zeroStep q with
          | none => simp [Skeleton.evalFrom, reindex, hz]
          | some next => simpa [Skeleton.evalFrom, reindex, hz] using ih next
      | oneZero =>
          cases ho : K.oneSignature q with
          | none => simp [Skeleton.evalFrom, reindex, ho]
          | some signature =>
              cases hr : signature.2 with
              | none => simp [Skeleton.evalFrom, reindex, ho, hr]
              | some next => simpa [Skeleton.evalFrom, reindex, ho, hr] using ih next

/-- Start-state evaluation is unchanged for the original block-code carrier. -/
theorem eval_reindex (K : Skeleton Output State) (e : State ≃ Target)
    (code : BlockCode) : (reindex K e).eval code = K.eval code :=
  evalFrom_reindex K e K.start code.blocks code.terminal

/-- The used signature itself transports along the same recurrent equivalence. -/
def signatureMap (K : Skeleton Output State) (e : State ≃ Target)
    (signature : SignatureFiber K) : SignatureFiber (reindex K e) :=
  ⟨(signature.1.1, signature.1.2.map e), by
    obtain ⟨q, hq⟩ := signature.2
    exact ⟨e q, by simp [reindex, hq]⟩⟩

/-- Renaming cannot identify two distinct used signatures. -/
theorem signatureMap_injective (K : Skeleton Output State) (e : State ≃ Target) :
    Function.Injective (signatureMap K e) := by
  intro a b h
  have hp := congrArg
    (fun p : Output × Option Target => (p.1, p.2.map e.symm))
    (congrArg Subtype.val h)
  apply Subtype.ext
  simpa [signatureMap, Option.map_map, Function.comp_def] using hp

/-- Every used signature of the reindexed machine comes from an old one. -/
theorem signatureMap_surjective (K : Skeleton Output State) (e : State ≃ Target) :
    Function.Surjective (signatureMap K e) := by
  intro signature
  obtain ⟨q, hq⟩ := signature.2
  change (K.oneSignature (e.symm q)).map
    (fun p => (p.1, p.2.map e)) = some signature.1 at hq
  obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp hq
  refine ⟨⟨p, e.symm q, hp⟩, ?_⟩
  exact Subtype.ext he

/-- State renaming preserves the exact canonical cost, including unused states. -/
theorem canonical_cost_reindex [Fintype Output] [Fintype State] [Fintype Target]
    (K : Skeleton Output State) (e : State ≃ Target) :
    Fintype.card (CanonicalState (reindex K e)) =
      Fintype.card (CanonicalState K) := by
  have hs := Fintype.card_congr e
  have hp := Fintype.card_congr (Equiv.ofBijective (signatureMap K e)
    ⟨signatureMap_injective K e, signatureMap_surjective K e⟩)
  rw [canonical_state_card_eq, canonical_state_card_eq]
  exact congrArg₂ Nat.add hs.symm hp.symm

/-- An explicit conjugacy certificate transfers the known zero-transition row. -/
theorem zero_row_conjugacy (K : Skeleton Output State) (e : State ≃ Target)
    (A : State → State) (B : Target → Target)
    (row : ∀ q, K.zeroStep q = some (A q))
    (conjugacy : ∀ q, e (A q) = B (e q)) (q : Target) :
    (reindex K e).zeroStep q = some (B q) := by
  simp only [reindex, row, Option.map_some]
  exact congrArg some (by simpa using conjugacy (e.symm q))

/-- A zero-loop anchor is preserved rather than assumed absent from the cover. -/
theorem initial_zero_loop_reindex (K : Skeleton Output State) (e : State ≃ Target)
    (loop : K.zeroStep K.start = some K.start) :
    (reindex K e).zeroStep (reindex K e).start = some (reindex K e).start := by
  simp [reindex, loop]

/-- A concrete finite zero-map cover reduces fixed-budget sample exclusion to
its representatives. Cover membership must be witnessed by a real equivalence;
no surjectivity of a canonicalizer is postulated. This is a reduction theorem,
not the executed numerical exclusion of any particular list of representatives. -/
theorem covered_zero_maps_refute_samples {r count : Nat}
    (root : Fin r) (maps : Fin count → Fin r → Fin r)
    (cover : ∀ A : Fin r → Fin r, A root = root →
      ∃ i : Fin count, ∃ e : Equiv.Perm (Fin r),
        e root = root ∧ ∀ q, e (A q) = maps i (e q))
    {Index : Type*} (codes : Index → BlockCode) (labels : Index → Fin 4)
    (budget : Nat)
    (excluded : ∀ i : Fin count,
      ¬ ∃ K : Skeleton (Fin 4) (Fin r),
        K.start = root ∧ (∀ q, K.zeroStep q = some (maps i q)) ∧
        K.zeroOutput K.start = 0 ∧
        Fintype.card (CanonicalState K) ≤ budget ∧
        ∀ j, K.eval (codes j) = some (labels j))
    (K : Skeleton (Fin 4) (Fin r)) (A : Fin r → Fin r)
    (start : K.start = root) (row : ∀ q, K.zeroStep q = some (A q))
    (fixed : A root = root) (zero : K.zeroOutput K.start = 0)
    (cost : Fintype.card (CanonicalState K) ≤ budget)
    (fits : ∀ j, K.eval (codes j) = some (labels j)) : False := by
  obtain ⟨i, e, he, hA⟩ := cover A fixed
  apply excluded i
  refine ⟨reindex K e, ?_, zero_row_conjugacy K e A (maps i) row hA, ?_, ?_, ?_⟩
  · simpa [reindex, start] using he
  · simpa [reindex] using zero
  · simpa only [canonical_cost_reindex] using cost
  · intro j
    simpa only [eval_reindex] using fits j

#print axioms evalFrom_reindex
#print axioms canonical_cost_reindex
#print axioms covered_zero_maps_refute_samples

end D5.S0.Automata.SkeletonStateConjugacy
