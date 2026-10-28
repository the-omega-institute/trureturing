/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeGuardedImageSaturation
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Simultaneous actual-image saturation for normalized guarded native systems. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedAtomicReplacement
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeImageSaturationInterface

/-! One actual guarded extension supplies all image filters simultaneously.
Only the finitely many small atomic free values remain fixed; every other
free value is replaced by the completed homogeneous tree Omega. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedImageSaturation

open NativeCompletionPrefixLifting CompletionHomogeneousFixedPoints
open NativeGuardedFreeExtension NativeGuardedAtomicReplacement
open NativeImageSaturationInterface

private theorem image_coinduction (k : Nat) (R : CompletionTree → Prop)
    (step : ∀ X, R X → X = atomic k ∨ X = atomic (k + 1) ∨
      ∃ U V, X = node U V ∧ R U ∧ R V) :
    ∀ X, R X → NativeImage k X := by
  classical
  let Q := {X : CompletionTree // R X}
  have split : ∀ q : Q, ∃ d : Bool ⊕ (Q × Q),
      match d with
      | .inl b => q.val = rho^[k] (leaf b)
      | .inr (u, v) => q.val = node u.val v.val := by
    intro q
    rcases step q.val q.property with h | h | ⟨U, V, h, hU, hV⟩
    · exact ⟨.inl true, h⟩
    · refine ⟨.inl false, ?_⟩
      rw [h]
      simp only [atomic, Function.iterate_succ_apply, rho_alpha]
    · exact ⟨.inr (⟨U, hU⟩, ⟨V, hV⟩), h⟩
  let pick (q : Q) := Classical.choose (split q)
  have sound (q : Q) := Classical.choose_spec (split q)
  let coalgebra (q : Q) : completionFunctor Q := match pick q with
    | .inl b => ⟨.inl b, Empty.elim⟩
    | .inr (u, v) => ⟨.inr (), fun b : Bool => if b then v else u⟩
  let pre (q : Q) : CompletionTree := PFunctor.M.corec coalgebra q
  have unfold_pre (q : Q) : pre q = match pick q with
      | .inl b => leaf b
      | .inr (u, v) => node (pre u) (pre v) := by
    change PFunctor.M.corec coalgebra q = _
    rw [PFunctor.M.corec_def]
    cases h : pick q with
    | inl b =>
      have cq : coalgebra q = ⟨.inl b, Empty.elim⟩ := by
        change (show completionFunctor Q from match pick q with
          | .inl b => ⟨.inl b, Empty.elim⟩
          | .inr (u, v) => ⟨.inr (), fun b : Bool => if b then v else u⟩) = _
        rw [h]
      rw [cq]
      simp only [PFunctor.map, leaf, Function.comp_def]
      apply congrArg PFunctor.M.mk
      simp only [PFunctor.Obj.mk, PFunctor.Obj.fst, PFunctor.Obj.snd]
      refine Sigma.ext (by rfl) ?_
      apply heq_of_eq
      funext e
      exact e.elim
    | inr pair =>
      rcases pair with ⟨u, v⟩
      have cq : coalgebra q = ⟨.inr (), fun b : Bool => if b then v else u⟩ := by
        change (show completionFunctor Q from match pick q with
          | .inl b => ⟨.inl b, Empty.elim⟩
          | .inr (u, v) => ⟨.inr (), fun b : Bool => if b then v else u⟩) = _
        rw [h]
      rw [cq]
      simp only [PFunctor.map, Function.comp_def]
      apply congrArg PFunctor.M.mk
      simp only [PFunctor.Obj.mk, PFunctor.Obj.fst, PFunctor.Obj.snd]
      refine Sigma.ext (by rfl) ?_
      apply heq_of_eq
      funext b
      cases b <;> rfl
  have prefixes : ∀ d (q : Q), cutoff d (rho^[k] (pre q)) = cutoff d q.val := by
    intro d
    induction d with
    | zero => intro q; rfl
    | succ d ih =>
      intro q
      have h := sound q
      change (match pick q with
        | .inl b => q.val = rho^[k] (leaf b)
        | .inr (u, v) => q.val = node u.val v.val) at h
      rw [unfold_pre]
      cases eq : pick q with
      | inl b => simp only [eq] at h ⊢; rw [h]
      | inr pair =>
        rcases pair with ⟨u, v⟩
        simp only [eq] at h ⊢
        rw [h, iterate_node]
        exact congrArg Sum.inr (congrArg₂ Prod.mk (ih u) (ih v))
  intro X hx
  refine ⟨pre ⟨X, hx⟩, ?_⟩
  apply readout_ext
  intro a
  exact (cutoff_readout (a.length + 1) _ _).mp (prefixes _ ⟨X, hx⟩) a (by omega)

private theorem image_shift_large (k a : Nat) (X : CompletionTree) (ha : k ≤ a) :
    NativeImage k (rho^[a] X) := by
  refine ⟨rho^[a - k] X, ?_⟩
  rw [← Function.iterate_add_apply, Nat.add_sub_of_le ha]

private theorem image_shift_cancel (k a : Nat) (X : CompletionTree) (ha : a ≤ k) :
    NativeImage k (rho^[a] X) ↔ NativeImage (k - a) X := by
  constructor
  · rintro ⟨Y, h⟩
    refine ⟨Y, (rho_injective.iterate a) ?_⟩
    rw [← Function.iterate_add_apply, Nat.add_sub_of_le ha]
    exact h
  · rintro ⟨Y, h⟩
    refine ⟨Y, ?_⟩
    rw [show k = a + (k - a) from (Nat.add_sub_of_le ha).symm,
      Function.iterate_add_apply, h]

/-- Fixed alternatives are the actual atoms through rank S+1; none denotes
all other completed values, including arbitrary non-rational trees. -/
abbrev Mode (S m : Nat) := Fin m → Option (Fin (S + 2))

def InMode {k m : Nat} (S : System k m) (s : Nat) (mode : Mode s m)
    (v : Fin m → CompletionTree) : Prop :=
  ∀ i, S i = none → match mode i with
    | some j => v i = atomic j.val
    | none => ∀ j, j ≤ s + 1 → v i ≠ atomic j

def canonicalFree {s m : Nat} (mode : Mode s m) (i : Fin m) : CompletionTree :=
  match mode i with
  | some j => atomic j.val
  | none => Omega

noncomputable def canonical {k m : Nat} (S : System k m) (p : Fin k → Nat)
    (guarded : Guarded S) {s : Nat} (mode : Mode s m) : Fin m → CompletionTree :=
  Classical.choose (guarded_extension S p guarded (canonicalFree mode)).exists

private theorem canonical_law {k m : Nat} (S : System k m) (p : Fin k → Nat)
    (guarded : Guarded S) {s : Nat} (mode : Mode s m) :
    Satisfies S p (canonical S p guarded mode) ∧
      Extends S (canonicalFree mode) (canonical S p guarded mode) :=
  Classical.choose_spec (guarded_extension S p guarded (canonicalFree mode)).exists

private theorem replacement_filters {k m : Nat} (S : System k m) (p : Fin k → Nat)
    (guarded : Guarded S) (s : Nat) (v w : Fin m → CompletionTree)
    (satV : Satisfies S p v) (satW : Satisfies S p w)
    (free : ∀ i, S i = none → w i = v i ∨ w i = Omega)
    (small : ∀ i, S i = none → ∀ j, j ≤ s + 1 → v i = atomic j → w i = v i) :
    ∀ t, t ≤ s → ∀ E : Expression k m,
      NativeImage t (evaluate p v E) → NativeImage t (evaluate p w E) := by
  have atoms := atomic_replacement S p guarded v w satV satW (s + 1) small
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro bound
    let R (X : CompletionTree) : Prop := NativeImage t X ∨
      ∃ E : Expression k m, X = evaluate p w E ∧ NativeImage t (evaluate p v E)
    have known : ∀ X, NativeImage t X → X = atomic t ∨ X = atomic (t + 1) ∨
        ∃ U V, X = node U V ∧ R U ∧ R V := by
      intro X hx
      rcases (native_image_iff t X).mp hx with h | h | ⟨U, V, eq, hU, hV⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨U, V, eq, Or.inl hU, Or.inl hV⟩)
    have pair_step : ∀ A B : Expression k m,
        NativeImage t (evaluate p v (.pair A B)) →
        evaluate p w (.pair A B) = atomic t ∨
        evaluate p w (.pair A B) = atomic (t + 1) ∨
        ∃ U V, evaluate p w (.pair A B) = node U V ∧ R U ∧ R V := by
      intro A B accept
      rcases (native_image_iff t _).mp accept with h | h | ⟨U, V, eq, hU, hV⟩
      · exact Or.inl ((atoms (.pair A B) t (by omega) h).trans h)
      · exact Or.inr (Or.inl ((atoms (.pair A B) (t + 1) (by omega) h).trans h))
      · have sides := node_inj eq
        refine Or.inr (Or.inr ⟨evaluate p w A, evaluate p w B, rfl, ?_, ?_⟩)
        · refine Or.inr ⟨A, rfl, ?_⟩
          change NativeImage t
            (CompletionPositiveDriftRegion.value (tokenKind k) (tokenRank p) v A)
          rw [sides.1]
          exact hU
        · refine Or.inr ⟨B, rfl, ?_⟩
          change NativeImage t
            (CompletionPositiveDriftRegion.value (tokenKind k) (tokenRank p) v B)
          rw [sides.2]
          exact hV
    have analyze : ∀ E : Expression k m, NativeImage t (evaluate p v E) →
        evaluate p w E = atomic t ∨ evaluate p w E = atomic (t + 1) ∨
        ∃ U V, evaluate p w E = node U V ∧ R U ∧ R V := by
      intro E accept
      cases E with
      | ground g => exact known _ accept
      | token j c => exact known _ accept
      | pair A B => exact pair_step A B accept
      | var a i =>
        cases a with
        | succ a =>
          apply known
          by_cases large : t ≤ a + 1
          · exact image_shift_large t (a + 1) (w i) large
          · have lower : a + 1 ≤ t := by omega
            have old := (image_shift_cancel t (a + 1) (v i) lower).mp accept
            have new := ih (t - (a + 1)) (by omega) (by omega)
              (.var 0 i) old
            exact (image_shift_cancel t (a + 1) (w i) lower).mpr new
        | zero =>
          change NativeImage t (v i) at accept
          change w i = atomic t ∨ w i = atomic (t + 1) ∨
            ∃ U V, w i = node U V ∧ R U ∧ R V
          cases eq : S i with
          | none =>
            apply known
            rcases free i eq with same | omega
            · exact same.symm ▸ accept
            · rw [omega]
              exact ⟨Omega, iterate_omega t⟩
          | some F =>
            rw [satW i F eq]
            rw [satV i F eq] at accept
            cases F with
            | ground g => exact known _ accept
            | token j c => exact known _ accept
            | pair A B => exact pair_step A B accept
            | var a j => exact (guarded i a j eq).elim
    have closed : ∀ X, R X → X = atomic t ∨ X = atomic (t + 1) ∨
        ∃ U V, X = node U V ∧ R U ∧ R V := by
      intro X hx
      rcases hx with accept | ⟨E, rfl, accept⟩
      · exact known X accept
      · exact analyze E accept
    intro E accept
    exact image_coinduction t R closed _ (Or.inr ⟨E, rfl, accept⟩)

abbrev Filter (k m : Nat) := Expression k m × Nat

def threshold {k m : Nat} (filters : List (Filter k m)) : Nat :=
  (filters.map Prod.snd).foldr max 0

def Passes {k m : Nat} (p : Fin k → Nat) (v : Fin m → CompletionTree)
    (filters : List (Filter k m)) : Prop :=
  ∀ E t, (E, t) ∈ filters → NativeImage t (evaluate p v E)

/-- All retained filters are tested jointly on one canonical extension of the
same normalized system, parameter, fixed atoms and live-free mode. -/
theorem normalized_saturation {k m : Nat} (S : System k m) (p : Fin k → Nat)
    (guarded : Guarded S) (filters : List (Filter k m))
    (mode : Mode (threshold filters) m) :
    Satisfies S p (canonical S p guarded mode) ∧
    InMode S (threshold filters) mode (canonical S p guarded mode) ∧
    ((∃ v, Satisfies S p v ∧ InMode S (threshold filters) mode v ∧ Passes p v filters) ↔
      Passes p (canonical S p guarded mode) filters) := by
  have law := canonical_law S p guarded mode
  have membership : InMode S (threshold filters) mode (canonical S p guarded mode) := by
    intro i hi
    rw [law.2 i hi]
    cases h : mode i with
    | some j => simp only [canonicalFree, h]
    | none =>
      simp only [canonicalFree, h]
      intro j hj eq
      exact CompletionPositiveDriftRegion.omega_not_finite
        (eq.symm ▸ CompletionPositiveDriftRegion.atomic_finite j)
  refine ⟨law.1, membership, ?_⟩
  constructor
  · rintro ⟨v, sat, vm, pass⟩
    have free : ∀ i, S i = none →
        canonical S p guarded mode i = v i ∨ canonical S p guarded mode i = Omega := by
      intro i hi
      rw [law.2 i hi]
      have h := vm i hi
      cases eq : mode i with
      | none => exact Or.inr (by simp only [canonicalFree, eq])
      | some j =>
        simp only [eq] at h
        exact Or.inl (by simpa only [canonicalFree, eq] using h.symm)
    have small : ∀ i, S i = none → ∀ j, j ≤ threshold filters + 1 →
        v i = atomic j → canonical S p guarded mode i = v i := by
      intro i hi j hj eq
      have h := vm i hi
      rw [law.2 i hi]
      cases hm : mode i with
      | none =>
        simp only [hm] at h
        exact (h j hj eq).elim
      | some l =>
        simp only [hm] at h
        simpa only [canonicalFree, hm] using h.symm
    have all_bounds : ∀ (L : List (Filter k m)) E t, (E, t) ∈ L → t ≤ threshold L := by
      intro L
      induction L with
      | nil => intro E t ht; simp at ht
      | cons f rest ih =>
        intro E t ht
        rcases List.mem_cons.mp ht with h | h
        · cases h
          exact Nat.le_max_left _ _
        · exact (ih E t h).trans (Nat.le_max_right _ _)
    intro E t ht
    exact replacement_filters S p guarded _ v _ sat law.1 free small t
      (all_bounds filters E t ht) E (pass E t ht)
  · intro pass
    exact ⟨canonical S p guarded mode, law.1, membership, pass⟩

end D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedImageSaturation
