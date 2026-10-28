/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeOriginalReconstructionBridge
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact syntactic epoch transport and canonical original-coordinate reconstruction. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeEffectiveImageGuard
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalCoordinatePrefix

/-! Original decorated equations, retained image filters and reconstructions
are transported by native powers. No semantic reconstruction identity is input. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeOriginalReconstructionBridge

open GenealogicalFiberTransport (Source substitution)
open NativeCompletionPrefixLifting CompletionHomogeneousFixedPoints
open NativeGuardedFreeExtension NativeGuardedImageSaturation
open NativeRootLinkNormalization NativeAffineImageSaturation NativeEffectiveImageGuard
open NativeImageSaturationInterface
open NativeSymbolicFiniteForcing (FunctionalSystem canonicalSolution finiteExpressions
  finiteOriginals finiteValue symbolic_finite_forcing)
open NativeOriginalCoordinatePrefix (terminalHeight decodePrefix decode_prefix_correct)
open NativeDepthPatterns (Pattern)

/-- The source equation at a defined head is rho^(headPower i) X_i = E_i.
The affine ranks, legal domain and all additional filters remain in base. -/
structure EpochInput (n k m : Nat) where
  base : Input n k m
  headPower : Fin m → Nat

def ShiftLegal {k m : Nat} (s : Fin m → Nat) (t : Nat) : Expression k m → Prop
  | .ground _ => True
  | .token _ _ => True
  | .var b j => s j ≤ b + t
  | .pair A B => ShiftLegal s t A ∧ ShiftLegal s t B

instance shiftLegalDecidable {k m : Nat} (s : Fin m → Nat) (t : Nat) :
    (E : Expression k m) → Decidable (ShiftLegal s t E)
  | .ground _ => isTrue trivial
  | .token _ _ => isTrue trivial
  | .var b j => inferInstanceAs (Decidable (s j ≤ b + t))
  | .pair A B =>
      letI := shiftLegalDecidable s t A
      letI := shiftLegalDecidable s t B
      inferInstanceAs (Decidable (ShiftLegal s t A ∧ ShiftLegal s t B))

/-- These are precisely the natural form of the NIS.11 potential inequalities. -/
def Potential {n k m : Nat} (I : EpochInput n k m) (s : Fin m → Nat) : Prop :=
  ∀ i E, I.base.equations i = some E →
    I.headPower i ≤ s i ∧ ShiftLegal s (s i - I.headPower i) E

/-- A distributed shift; the legality proof is kept separately and decidable. -/
def transport {k m : Nat} (s : Fin m → Nat) (t : Nat) :
    Expression k m → Expression k m
  | .ground g => .ground (substitution^[t] g)
  | .token j c => .token j (t + c)
  | .var b j => .var (b + t - s j) j
  | .pair A B => .pair (transport s t A) (transport s t B)

def imageValues {m : Nat} (s : Fin m → Nat) (v : Fin m → CompletionTree) :
    Fin m → CompletionTree := fun i => rho^[s i] (v i)

private theorem transport_value {k m : Nat} (s : Fin m → Nat) (t : Nat)
    (p : Fin k → Nat) (v : Fin m → CompletionTree) (E : Expression k m)
    (legal : ShiftLegal s t E) :
    evaluate p (imageValues s v) (transport s t E) = rho^[t] (evaluate p v E) := by
  induction E with
  | ground g => exact (iterate_embed t g).symm
  | token j c =>
      change (if tokenKind k j then atomic (tokenRank p j + (t + c)) else Omega) =
        rho^[t] (if tokenKind k j then atomic (tokenRank p j + c) else Omega)
      cases h : tokenKind k j
      · simp only [Bool.false_eq_true, ite_false, iterate_omega]
      · simp only [ite_true, atomic, ← Function.iterate_add_apply]
        congr 1
        omega
  | var b j =>
      change rho^[b + t - s j] (rho^[s j] (v j)) = rho^[t] (rho^[b] (v j))
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
      congr 1
      dsimp [ShiftLegal] at legal
      omega
  | pair A B ihA ihB =>
      change node (evaluate p (imageValues s v) (transport s t A))
        (evaluate p (imageValues s v) (transport s t B)) =
          rho^[t] (node (evaluate p v A) (evaluate p v B))
      rw [ihA legal.1, ihB legal.2, iterate_node]

/-- One input-derived shift works for every reconstruction and additional filter. -/
def commonShift {m : Nat} (s : Fin m → Nat) : Nat :=
  ((List.finRange m).map s).foldr max 0

private theorem commonShift_bound {m : Nat} (s : Fin m → Nat) (i : Fin m) :
    s i ≤ commonShift s := by
  have member : s i ∈ (List.finRange m).map s := List.mem_map.mpr ⟨i, by simp, rfl⟩
  unfold commonShift
  generalize (List.finRange m).map s = l at member ⊢
  change s i ≤ l.foldr max 0
  induction l with
  | nil => cases member
  | cons a l ih =>
      rcases List.mem_cons.mp member with ha | hl
      · exact ha ▸ Nat.le_max_left _ _
      · exact (ih hl).trans (Nat.le_max_right _ _)

private theorem commonShift_legal {k m : Nat} (s : Fin m → Nat) (E : Expression k m) :
    ShiftLegal s (commonShift s) E := by
  induction E with
  | ground _ => trivial
  | token _ _ => trivial
  | var b j => exact (commonShift_bound s j).trans (by omega)
  | pair A B ihA ihB => exact ⟨ihA, ihB⟩

def functionalInput {n k m : Nat} (I : EpochInput n k m) (s : Fin m → Nat) :
    Input n k m where
  equations := fun i => (I.base.equations i).map
    (transport s (s i - I.headPower i))
  filters := (List.finRange m).map (fun i => ((.var 0 i : Expression k m), s i)) ++
    I.base.filters.map (fun f => (transport s (commonShift s) f.1, f.2 + commonShift s))
  indices := I.base.indices
  guard := I.base.guard

def OriginalSatisfies {n k m : Nat} (I : EpochInput n k m) (p : Fin n → Nat)
    (v : Fin m → CompletionTree) : Prop :=
  ∀ i E, I.base.equations i = some E →
    rho^[I.headPower i] (v i) = evaluate (ranks I.base p) v E

def OriginalAdmissible {n k m : Nat} (I : EpochInput n k m) (p : Fin n → Nat)
    (v : Fin m → CompletionTree) : Prop :=
  Legal I.base p ∧ OriginalSatisfies I p v ∧ SourcePasses I.base p v

private theorem equation_correspond {n k m : Nat} (I : EpochInput n k m)
    (s : Fin m → Nat) (valid : Potential I s) (p : Fin n → Nat)
    (v : Fin m → CompletionTree) :
    OriginalSatisfies I p v ↔ SourceSatisfies (functionalInput I s) p (imageValues s v) := by
  constructor
  · intro sat i F eq
    obtain ⟨E, he, rfl⟩ := Option.map_eq_some_iff.mp eq
    have hv := valid i E he
    change rho^[s i] (v i) = evaluate (ranks I.base p) (imageValues s v)
      (transport s (s i - I.headPower i) E)
    rw [transport_value s _ _ _ _ hv.2, ← sat i E he, ← Function.iterate_add_apply]
    congr 1
    omega
  · intro sat i E he
    have hv := valid i E he
    have law := sat i (transport s (s i - I.headPower i) E)
      (by simp only [functionalInput, he, Option.map_some])
    change rho^[s i] (v i) = evaluate (ranks I.base p) (imageValues s v)
      (transport s (s i - I.headPower i) E) at law
    rw [transport_value s _ _ _ _ hv.2] at law
    apply (rho_injective.iterate (s i - I.headPower i))
    rw [← Function.iterate_add_apply]
    convert law using 1
    congr 1
    omega

private theorem image_shift_iff (r t : Nat) (X : CompletionTree) :
    NativeImage (r + t) (rho^[t] X) ↔ NativeImage r X := by
  constructor
  · rintro ⟨Y, hy⟩
    refine ⟨Y, (rho_injective.iterate t) ?_⟩
    simpa only [Nat.add_comm r t, Function.iterate_add_apply] using hy
  · rintro ⟨Y, rfl⟩
    exact ⟨Y, by rw [Nat.add_comm r t, Function.iterate_add_apply]⟩

private theorem filters_correspond_epoch {n k m : Nat} (I : EpochInput n k m)
    (s : Fin m → Nat) (p : Fin n → Nat) (v : Fin m → CompletionTree) :
    SourcePasses (functionalInput I s) p (imageValues s v) ↔ SourcePasses I.base p v := by
  constructor
  · intro pass E r hr
    have h := pass (transport s (commonShift s) E) (r + commonShift s)
      (List.mem_append_right _ (List.mem_map.mpr ⟨(E,r), hr, rfl⟩))
    change NativeImage (r + commonShift s)
      (evaluate (ranks I.base p) (imageValues s v) (transport s (commonShift s) E)) at h
    rw [transport_value s _ _ _ _ (commonShift_legal s E)] at h
    exact (image_shift_iff _ _ _).mp h
  · intro pass E r hr
    rcases List.mem_append.mp hr with state | additional
    · obtain ⟨i, hi, eq⟩ := List.mem_map.mp state
      cases eq
      exact ⟨v i, rfl⟩
    · obtain ⟨⟨F,u⟩, hf, eq⟩ := List.mem_map.mp additional
      cases eq
      change NativeImage (u + commonShift s)
        (evaluate (ranks I.base p) (imageValues s v) (transport s (commonShift s) F))
      rw [transport_value s _ _ _ _ (commonShift_legal s F)]
      exact (image_shift_iff _ _ _).mpr (pass F u hf)

/-- The complete original relation corresponds exactly to the transformed
relation. Every state-image filter and every additional filter is retained. -/
theorem epoch_solution_correspondence {n k m : Nat} (I : EpochInput n k m)
    (s : Fin m → Nat) (valid : Potential I s) (p : Fin n → Nat)
    (w : Fin m → CompletionTree) :
    (Legal (functionalInput I s) p ∧ SourceSatisfies (functionalInput I s) p w ∧
      SourcePasses (functionalInput I s) p w) ↔
    ∃! v, OriginalAdmissible I p v ∧ imageValues s v = w := by
  constructor
  · rintro ⟨legal, sat, pass⟩
    have images : ∀ i, ∃ X, rho^[s i] X = w i := by
      intro i
      exact pass (.var 0 i) (s i)
        (List.mem_append_left _ (List.mem_map.mpr ⟨i, by simp, rfl⟩))
    choose v hv using images
    have eq : imageValues s v = w := funext hv
    have admissible : OriginalAdmissible I p v := by
      refine ⟨legal, (equation_correspond I s valid p v).mpr ?_,
        (filters_correspond_epoch I s p v).mp ?_⟩ <;> rwa [eq]
    refine ⟨v, ⟨admissible, eq⟩, ?_⟩
    intro u hu
    funext i
    exact (rho_injective.iterate (s i))
      ((congrFun hu.2 i).trans (hv i).symm)
  · rintro ⟨v, ⟨admissible, rfl⟩, unique⟩
    exact ⟨admissible.1, (equation_correspond I s valid p v).mp admissible.2.1,
      (filters_correspond_epoch I s p v).mpr admissible.2.2⟩

/-- Every arbitrary original expression has this literal common-shift image,
independently of the equation system and without a supplied bridge identity. -/
theorem reconstruction_transport {k m : Nat} (s : Fin m → Nat)
    (p : Fin k → Nat) (v : Fin m → CompletionTree) (E : Expression k m) :
    evaluate p (imageValues s v) (transport s (commonShift s) E) =
      rho^[commonShift s] (evaluate p v E) ∧
    NativeImage (commonShift s)
      (evaluate p (imageValues s v) (transport s (commonShift s) E)) := by
  have eq := transport_value s _ p v E (commonShift_legal s E)
  exact ⟨eq, evaluate p v E, eq.symm⟩

/-- Fix only the exceptional finite free states. Live states stay undefined,
so their alternative completed values remain unrestricted. -/
def fixedSystem {k m a : Nat} (S : System k m) (mode : Mode a m) : System k m :=
  fun i => match S i with
  | some E => some E
  | none => (mode i).map fun j => .ground (substitution^[j.val] (.of true))

private theorem fixed_solution {k m a : Nat} (S : System k m) (mode : Mode a m)
    (p : Fin k → Nat) (v : Fin m → CompletionTree)
    (sat : Satisfies S p v) (vm : InMode S a mode v) :
    NativeSymbolicFiniteForcing.satisfies (fixedSystem S mode) (tokenKind k) (tokenRank p) v := by
  intro i E eq
  cases hs : S i with
  | some F =>
      have same : F = E := by simpa only [fixedSystem, hs, Option.some.injEq] using eq
      subst E
      exact sat i F hs
  | none =>
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [fixedSystem, hs] using eq)
      have same := vm i hs
      simp only [hj] at same
      exact same.trans (iterate_embed j.val (.of true))

private theorem canonical_undefined {k m : Nat} (S : FunctionalSystem k m)
    (mode : Fin k → Bool) (p : Fin k → Nat) (i : Fin m) (empty : S i = none) :
    canonicalSolution S mode p i = Omega := by
  apply NativeFunctionalObstruction.leafLimit_unique
    (NativeSymbolicFiniteForcing.canonical_limit _ _)
  have all : ∀ n, NativeSymbolicFiniteForcing.approximants
      (NativeSymbolicFiniteForcing.nativeSystem S mode p) n i.castSucc = Omega := by
    intro n
    cases n with
    | zero => rfl
    | succ n =>
        simp [NativeSymbolicFiniteForcing.approximants,
          NativeFunctionalObstruction.extensionIterate,
          NativeFunctionalObstruction.extensionStep,
          NativeSymbolicFiniteForcing.nativeSystem, empty]
  intro q b
  simp only [all]
  exact ⟨fun h => ⟨0, h⟩, fun ⟨_, h⟩ => h⟩

private theorem fixed_canonical {k m a : Nat} (S : System k m) (guarded : Guarded S)
    (mode : Mode a m) (p : Fin k → Nat) :
    canonicalSolution (fixedSystem S mode) (tokenKind k) (tokenRank p) =
      canonical S p guarded mode := by
  let v := canonicalSolution (fixedSystem S mode) (tokenKind k) (tokenRank p)
  have law := (symbolic_finite_forcing (fixedSystem S mode) (tokenKind k)
    (fun i : Fin 0 => Fin.elim0 i)).1 (tokenRank p)
  have sat : Satisfies S p v := by
    intro i E eq
    exact law i E (by simp only [fixedSystem, eq])
  have free : Extends S (canonicalFree mode) v := by
    intro i hi
    cases hm : mode i with
    | none =>
        simp only [canonicalFree, hm]
        exact canonical_undefined (fixedSystem S mode) (tokenKind k) (tokenRank p) i
          (by simp only [fixedSystem, hi, hm, Option.map_none])
    | some j =>
        simp only [canonicalFree, hm]
        have eqn := law i (.ground (substitution^[j.val] (.of true)))
          (by simp only [fixedSystem, hi, hm, Option.map_some])
        exact eqn.trans (iterate_embed j.val (.of true)).symm
  obtain ⟨w, hw, unique⟩ := guarded_extension S p guarded (canonicalFree mode)
  exact (unique v ⟨sat, free⟩).trans
    (unique (canonical S p guarded mode) (canonical_law S p guarded mode)).symm

/-- The effective root presentation is computed from the transformed equations. -/
def presentation {n k m : Nat} (I : EpochInput n k m) (s : Fin m → Nat) :
    Presentation k m := effectiveNormalForm (functionalInput I s).equations

def reconstructionImages {n k m r : Nat} (I : EpochInput n k m) (s : Fin m → Nat)
    (R : Fin r → Expression k m) : Fin r → Expression k m :=
  fun i => substitute (presentation I s).reconstruct (transport s (commonShift s) (R i))

def canonicalSystem {n k m : Nat} (I : EpochInput n k m) (s : Fin m → Nat)
    (mode : EffectiveMode (functionalInput I s)) : System k m :=
  fixedSystem (presentation I s).equations (effectiveTotalMode (functionalInput I s) mode)

def finiteReconstructions {n k m r : Nat} (I : EpochInput n k m) (s : Fin m → Nat)
    (mode : EffectiveMode (functionalInput I s)) (R : Fin r → Expression k m) :
    Finset (Fin r) := finiteOriginals (canonicalSystem I s mode) (tokenKind k)
      (reconstructionImages I s R)

def finiteImageExpressions {n k m r : Nat} (I : EpochInput n k m) (s : Fin m → Nat)
    (mode : EffectiveMode (functionalInput I s)) (R : Fin r → Expression k m) :
    Fin r → Option (NativeSymbolicFiniteForcing.FiniteExpression (k + 1)) :=
  finiteExpressions (canonicalSystem I s mode) (tokenKind k) (reconstructionImages I s R)

/-- The actual finite image evaluator is run through inclusive depth H_t+h;
its pattern cutoff is H_t+h+1 = H_t+(h+1), including h=0 and t=0. -/
def originalPrefixProgram {n k m r : Nat} (I : EpochInput n k m) (s : Fin m → Nat)
    (mode : EffectiveMode (functionalInput I s)) (p : Fin n → Nat)
    (R : Fin r → Expression k m) (h : Nat) (i : Fin r) : Pattern (h + 1) :=
  decodePrefix (commonShift s) (h + 1)
    (NativeFunctionalEffectivePrefix.prefixProgram (canonicalSystem I s mode) (tokenKind k)
      (tokenRank (ranks I.base p)) (reconstructionImages I s R)
      (terminalHeight (commonShift s) + h) i)

private theorem canonical_image_law {n k m : Nat} (I : EpochInput n k m)
    (s : Fin m → Nat) (valid : Potential I s) (mode : EffectiveMode (functionalInput I s))
    (p : Fin n → Nat)
    (passing : (originalImageGuard (functionalInput I s) mode).holds (environment p)) :
    ∃! v, OriginalAdmissible I p v ∧
      imageValues s v = effectiveCanonical (functionalInput I s) mode p := by
  have accepted := ((original_effective_image_guard (functionalInput I s) mode p).1).mp passing
  have normal := effectiveNormalForm_law (functionalInput I s).equations
  have law := canonical_law (presentation I s).equations (ranks I.base p) normal.1
    (effectiveTotalMode (functionalInput I s) mode)
  have back := (normal.2 (ranks I.base p)).2 _ law.1
  exact (epoch_solution_correspondence I s valid p _).mp ⟨accepted.1, back.1, accepted.2⟩

noncomputable def canonicalOriginal {n k m : Nat} (I : EpochInput n k m)
    (s : Fin m → Nat) (valid : Potential I s) (mode : EffectiveMode (functionalInput I s))
    (p : Fin n → Nat)
    (passing : (originalImageGuard (functionalInput I s) mode).holds (environment p)) :
    Fin m → CompletionTree := Classical.choose (canonical_image_law I s valid mode p passing).exists

private theorem canonical_original_law {n k m : Nat} (I : EpochInput n k m)
    (s : Fin m → Nat) (valid : Potential I s) (mode : EffectiveMode (functionalInput I s))
    (p : Fin n → Nat)
    (passing : (originalImageGuard (functionalInput I s) mode).holds (environment p)) :
    OriginalAdmissible I p (canonicalOriginal I s valid mode p passing) ∧
      imageValues s (canonicalOriginal I s valid mode p passing) =
        effectiveCanonical (functionalInput I s) mode p :=
  Classical.choose_spec (canonical_image_law I s valid mode p passing).exists

theorem canonical_reconstruction_image {n k m r : Nat} (I : EpochInput n k m)
    (s : Fin m → Nat) (valid : Potential I s) (mode : EffectiveMode (functionalInput I s))
    (p : Fin n → Nat)
    (passing : (originalImageGuard (functionalInput I s) mode).holds (environment p))
    (R : Fin r → Expression k m) (i : Fin r) :
    CompletionPositiveDriftRegion.value (tokenKind k) (tokenRank (ranks I.base p))
      (canonicalSolution (canonicalSystem I s mode) (tokenKind k) (tokenRank (ranks I.base p)))
      (reconstructionImages I s R i) =
      rho^[commonShift s] (evaluate (ranks I.base p)
        (canonicalOriginal I s valid mode p passing) (R i)) := by
  have normal := effectiveNormalForm_law (functionalInput I s).equations
  rw [show canonicalSystem I s mode = fixedSystem (presentation I s).equations
    (effectiveTotalMode (functionalInput I s) mode) from rfl,
    fixed_canonical (presentation I s).equations normal.1
      (effectiveTotalMode (functionalInput I s) mode) (ranks I.base p)]
  change evaluate (ranks I.base p) _
    (substitute (presentation I s).reconstruct (transport s (commonShift s) (R i))) = _
  rw [substitute_value]
  change evaluate (ranks I.base p) (effectiveCanonical (functionalInput I s) mode p) _ = _
  rw [← (canonical_original_law I s valid mode p passing).2]
  exact (reconstruction_transport s _ _ (R i)).1

/-- Canonical classification and rigidity on the actual passing source mode,
and a total executable prefix program for its original reconstructions. The
infinite branch imposes no infiniteness condition on alternative solutions. -/
theorem original_classification_rigidity_prefix {n k m r : Nat} (I : EpochInput n k m)
    (s : Fin m → Nat) (valid : Potential I s) (mode : EffectiveMode (functionalInput I s))
    (R : Fin r → Expression k m) (p : Fin n → Nat)
    (passing : (originalImageGuard (functionalInput I s) mode).holds (environment p)) :
    OriginalAdmissible I p (canonicalOriginal I s valid mode p passing) ∧
    ∀ i : Fin r,
      (IsFinite (evaluate (ranks I.base p) (canonicalOriginal I s valid mode p passing) (R i)) ↔
        i ∈ finiteReconstructions I s mode R) ∧
      (i ∈ finiteReconstructions I s mode R →
        ∃ g : Source,
          evaluate (ranks I.base p) (canonicalOriginal I s valid mode p passing) (R i) = embed g ∧
          ∀ v, OriginalAdmissible I p v →
            EffectiveInMode (functionalInput I s) mode p (imageValues s v) →
            evaluate (ranks I.base p) v (R i) = embed g) ∧
      (∀ h, originalPrefixProgram I s mode p R h i = cutoff (h + 1)
        (evaluate (ranks I.base p) (canonicalOriginal I s valid mode p passing) (R i))) := by
  have forcing := symbolic_finite_forcing (canonicalSystem I s mode) (tokenKind k)
    (reconstructionImages I s R)
  have normal := effectiveNormalForm_law (functionalInput I s).equations
  refine ⟨(canonical_original_law I s valid mode p passing).1, ?_⟩
  intro i
  have image := canonical_reconstruction_image I s valid mode p passing R i
  have classify := (forcing.2 (tokenRank (ranks I.base p)) i).1
  rw [image, finite_iterate_iff] at classify
  refine ⟨classify, ?_, ?_⟩
  · intro finite
    obtain ⟨g, hg⟩ := classify.mpr finite
    refine ⟨g, hg.symm, ?_⟩
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp finite).2
    have forced := (forcing.2 (tokenRank (ranks I.base p)) i).2 f hf
    intro v admissible vm
    have forward := (normal.2 (ranks I.base p)).1 (imageValues s v)
      ((equation_correspond I s valid p v).mp admissible.2.1)
    have fixed := fixed_solution (presentation I s).equations
      (effectiveTotalMode (functionalInput I s) mode) (ranks I.base p) _ forward.1 vm
    have value := forced.2 _ fixed
    change evaluate (ranks I.base p) _
      (substitute (presentation I s).reconstruct (transport s (commonShift s) (R i))) = _ at value
    rw [substitute_value] at value
    dsimp only [presentation] at value
    rw [forward.2] at value
    rw [(reconstruction_transport s _ v (R i)).1] at value
    apply (rho_injective.iterate (commonShift s))
    rw [value, ← forced.1, image, ← hg]
  · intro h
    unfold originalPrefixProgram
    rw [NativeFunctionalEffectivePrefix.effective_prefix, image]
    exact decode_prefix_correct (commonShift s) (h + 1) _

#print axioms epoch_solution_correspondence
#print axioms reconstruction_transport
#print axioms original_classification_rigidity_prefix

end D5.S3.Arith.FibonacciAtomic.Observer.NativeOriginalReconstructionBridge
