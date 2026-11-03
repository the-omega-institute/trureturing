/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeRootLinkNormalization
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Two-sided native root-link elimination with every original reconstruction. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedImageSaturation

/-! Optional definitions may have arbitrary decorated root links. Eliminated
coordinates occupy inert ground slots; their original values are retained by
explicit reconstruction expressions. These slots add no free parameter. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeRootLinkNormalization

open NativeCompletionPrefixLifting CompletionHomogeneousFixedPoints
open NativeGuardedFreeExtension
open GenealogicalFiberTransport (Source substitution)

/-- Distribute one fixed native power without unfolding any state definition. -/
def shift {k m : Nat} (a : Nat) : Expression k m → Expression k m
  | .ground t => .ground (substitution^[a] t)
  | .token j c => .token j (a + c)
  | .var b j => .var (a + b) j
  | .pair A B => .pair (shift a A) (shift a B)

theorem shift_value {k m : Nat} (p : Fin k → Nat)
    (v : Fin m → CompletionTree) (a : Nat) (E : Expression k m) :
    evaluate p v (shift a E) = rho^[a] (evaluate p v E) := by
  induction E with
  | ground t => exact (iterate_embed a t).symm
  | token j c =>
    change (if tokenKind k j then atomic (tokenRank p j + (a + c)) else Omega) =
      rho^[a] (if tokenKind k j then atomic (tokenRank p j + c) else Omega)
    cases h : tokenKind k j
    · simp only [Bool.false_eq_true, ite_false, iterate_omega]
    · simp only [ite_true, atomic, ← Function.iterate_add_apply]
      congr 1
      omega
  | var b j => exact Function.iterate_add_apply rho a b (v j)
  | pair A B ihA ihB =>
    change node (evaluate p v (shift a A)) (evaluate p v (shift a B)) =
      rho^[a] (node (evaluate p v A) (evaluate p v B))
    rw [ihA, ihB, iterate_node]

/-- Simultaneous substitution retains ordered pairs and repeated occurrences. -/
def substitute {k m : Nat} (R : Fin m → Expression k m) : Expression k m → Expression k m
  | .ground t => .ground t
  | .token j c => .token j c
  | .var a j => shift a (R j)
  | .pair A B => .pair (substitute R A) (substitute R B)

def mapValues {k m : Nat} (p : Fin k → Nat) (R : Fin m → Expression k m)
    (v : Fin m → CompletionTree) : Fin m → CompletionTree :=
  fun i => evaluate p v (R i)

theorem substitute_value {k m : Nat} (p : Fin k → Nat)
    (R : Fin m → Expression k m) (v : Fin m → CompletionTree) (E : Expression k m) :
    evaluate p v (substitute R E) = evaluate p (mapValues p R v) E := by
  induction E with
  | ground t => rfl
  | token j c => rfl
  | var a j => exact shift_value p v a (R j)
  | pair A B ihA ihB => exact congrArg₂ node ihA ihB

def identity {k m : Nat} : Fin m → Expression k m := fun i => .var 0 i

private theorem map_compose {k m : Nat} (p : Fin k → Nat)
    (R P : Fin m → Expression k m) (v : Fin m → CompletionTree) :
    mapValues p (fun i => substitute R (P i)) v =
      mapValues p P (mapValues p R v) := by
  funext i
  exact substitute_value p R v (P i)

/-- A presentation keeps both finite expression maps, not a chosen solution. -/
structure Presentation (k m : Nat) where
  equations : System k m
  reconstruct : Fin m → Expression k m
  project : Fin m → Expression k m

/-- The two maps are mutually inverse on the full solution sets, at every
finite parameter tuple. Infinite values need not have finite descriptions. -/
def Correct {k m : Nat} (S : System k m) (T : Presentation k m) : Prop :=
  ∀ p : Fin k → Nat,
    (∀ v, Satisfies S p v →
      Satisfies T.equations p (mapValues p T.project v) ∧
      mapValues p T.reconstruct (mapValues p T.project v) = v) ∧
    (∀ w, Satisfies T.equations p w →
      Satisfies S p (mapValues p T.reconstruct w) ∧
      mapValues p T.project (mapValues p T.reconstruct w) = w)

private theorem positive_period (a : Nat) (positive : 0 < a)
    (X : CompletionTree) (fixed : X = rho^[a] X) : X = Omega := by
  have periods : ∀ r, rho^[r * a] X = X := by
    intro r
    induction r with
    | zero => simp only [Nat.zero_mul, Function.iterate_zero_apply]
    | succ r ih => rw [Nat.succ_mul, Function.iterate_add_apply, ← fixed, ih]
  apply eq_omega_of_full
  intro n
  have bound : 2 * n ≤ 2 * n * a := Nat.le_mul_of_pos_right _ positive
  rw [← periods (2 * n), show 2 * n * a = 2 * n + (2 * n * a - 2 * n) by omega,
    Function.iterate_add_apply]
  exact iterate_full n _

def selfStep {k m : Nat} (S : System k m) (i : Fin m) (a : Nat) :
    Presentation k m where
  equations := Function.update S i (if a = 0 then none else some (.token (Fin.last k) 0))
  reconstruct := identity
  project := identity

theorem selfStep_correct {k m : Nat} (S : System k m) (i : Fin m) (a : Nat)
    (eq : S i = some (.var a i)) : Correct S (selfStep S i a) := by
  intro p
  have omega_eval (v : Fin m → CompletionTree) :
      evaluate p v (.token (Fin.last k) 0) = Omega := by
    simp only [evaluate, CompletionPositiveDriftRegion.value, tokenKind,
      Fin.lastCases_last, Bool.false_eq_true, ite_false]
  constructor
  · intro v sat
    refine ⟨?_, rfl⟩
    intro j E defn
    by_cases ji : j = i
    · subst j
      by_cases az : a = 0
      · simp only [selfStep, Function.update_self, az, ite_true] at defn
        cases defn
      · have ee : E = .token (Fin.last k) 0 := by
          simpa only [selfStep, Function.update_self, az, ite_false, Option.some.injEq]
            using defn.symm
        subst E
        exact (positive_period a (by omega) (v i) (sat i _ eq)).trans (omega_eval v).symm
    · exact sat j E (by simpa only [selfStep, Function.update_of_ne ji] using defn)
  · intro w sat
    refine ⟨?_, rfl⟩
    intro j E defn
    by_cases ji : j = i
    · subst j
      have ee : E = .var a i := Option.some.inj (defn.symm.trans eq)
      subst E
      by_cases az : a = 0
      · subst a; rfl
      · have law := sat i (.token (Fin.last k) 0)
          (by simp only [selfStep, Function.update_self, az, ite_false])
        have wi : w i = Omega := law.trans (omega_eval w)
        change w i = rho^[a] (w i)
        rw [wi, iterate_omega]
    · exact sat j E (by simpa only [selfStep, Function.update_of_ne ji] using defn)

private def linkRecon {k m : Nat} (i : Fin m) (a : Nat) (j : Fin m) :
    Fin m → Expression k m := fun t => if t = i then .var a j else .var 0 t

private def linkProject {k m : Nat} (i : Fin m) : Fin m → Expression k m :=
  fun t => if t = i then .ground (.of true) else .var 0 t

def linkStep {k m : Nat} (S : System k m) (i : Fin m) (a : Nat) (j : Fin m) :
    Presentation k m where
  equations := fun t => if t = i then some (.ground (.of true))
    else (S t).map (substitute (linkRecon i a j))
  reconstruct := linkRecon i a j
  project := linkProject i

theorem linkStep_correct {k m : Nat} (S : System k m) (i : Fin m) (a : Nat)
    (j : Fin m) (ji : j ≠ i) (eq : S i = some (.var a j)) :
    Correct S (linkStep S i a j) := by
  classical
  unfold Correct
  dsimp only [linkStep]
  intro p
  have project (v : Fin m → CompletionTree) (t : Fin m) :
      mapValues p (linkProject i) v t = if t = i then leaf true else v t := by
    by_cases ti : t = i <;> simp only [mapValues, linkProject, ti, ite_true, ite_false]
    <;> rfl
  have recon (v : Fin m → CompletionTree) (t : Fin m) :
      mapValues p (linkRecon i a j) v t = if t = i then rho^[a] (v j) else v t := by
    by_cases ti : t = i <;> simp only [mapValues, linkRecon, ti, ite_true, ite_false]
    <;> rfl
  constructor
  · intro v sat
    have back : mapValues p (linkRecon i a j) (mapValues p (linkProject i) v) = v := by
      funext t
      rw [recon]
      by_cases ti : t = i
      · subst t
        simp only [ite_true, project, ji, ite_false]
        exact (sat i _ eq).symm
      · simp only [ti, ite_false, project]
    refine ⟨?_, back⟩
    intro t E defn
    change (if t = i then some (.ground (.of true))
      else (S t).map (substitute (linkRecon i a j))) = some E at defn
    by_cases ti : t = i
    · simp only [ti, ite_true, Option.some.injEq] at defn
      rw [← defn, project]
      simp only [ti, ite_true]
      rfl
    · simp only [ti, ite_false, Option.map_eq_some_iff] at defn
      obtain ⟨F, sf, rfl⟩ := defn
      rw [project, ite_eq_right ti, substitute_value, back]
      exact sat t F sf
  · intro w sat
    have dummy : w i = leaf true := sat i (.ground (.of true)) (by simp only [ite_true])
    have back : mapValues p (linkProject i) (mapValues p (linkRecon i a j) w) = w := by
      funext t
      rw [project]
      by_cases ti : t = i
      · subst t; simp only [ite_true]; exact dummy.symm
      · simp only [ti, ite_false, recon]
    refine ⟨?_, back⟩
    intro t E defn
    by_cases ti : t = i
    · subst t
      have ee : E = .var a j := Option.some.inj (defn.symm.trans eq)
      subst E
      change mapValues p (linkRecon i a j) w i =
        rho^[a] (mapValues p (linkRecon i a j) w j)
      rw [recon, recon]
      simp only [ite_true, ji, ite_false]
    · rw [recon, ite_eq_right ti, ← substitute_value]
      exact sat t _ (by simp only [ti, ite_false, defn, Option.map_some])

noncomputable def roots {k m : Nat} (S : System k m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i => ∃ a j, S i = some (.var a j)

theorem mem_roots {k m : Nat} (S : System k m) (i : Fin m) :
    i ∈ roots S ↔ ∃ a j, S i = some (.var a j) := by
  classical
  simp only [roots, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem substitution_root {k m : Nat} (R : Fin m → Expression k m)
    (E : Expression k m) (a : Nat) (j : Fin m) (eq : substitute R E = .var a j) :
    ∃ b t, E = .var b t := by
  cases E with
  | ground t => cases eq
  | token i c => cases eq
  | var b t => exact ⟨b, t, rfl⟩
  | pair A B => cases eq

theorem selfStep_decreases {k m : Nat} (S : System k m) (i : Fin m) (a : Nat)
    (eq : S i = some (.var a i)) :
    (roots (selfStep S i a).equations).card < (roots S).card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  have absent : i ∉ roots (selfStep S i a).equations := by
    rw [mem_roots]
    rintro ⟨b, j, h⟩
    by_cases az : a = 0 <;>
      simp only [selfStep, Function.update_self, az, ite_true, ite_false] at h <;> cases h
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨b, j, h⟩ := (mem_roots _ _).mp ht
    by_cases ti : t = i
    · exact (absent (ti ▸ ht)).elim
    · exact (mem_roots S t).mpr ⟨b, j, by
        simpa only [selfStep, Function.update_of_ne ti] using h⟩
  · intro equal
    exact absent (equal.symm ▸ (mem_roots S i).mpr ⟨a, i, eq⟩)

theorem linkStep_decreases {k m : Nat} (S : System k m) (i : Fin m) (a : Nat)
    (j : Fin m) (eq : S i = some (.var a j)) :
    (roots (linkStep S i a j).equations).card < (roots S).card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  have absent : i ∉ roots (linkStep S i a j).equations := by
    rw [mem_roots]
    rintro ⟨b, t, h⟩
    simp only [linkStep, ite_true] at h
    cases h
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨b, u, h⟩ := (mem_roots _ _).mp ht
    by_cases ti : t = i
    · exact (absent (ti ▸ ht)).elim
    · simp only [linkStep, ti, ite_false, Option.map_eq_some_iff] at h
      obtain ⟨E, se, ee⟩ := h
      obtain ⟨c, v, rfl⟩ := substitution_root _ E b u ee
      exact (mem_roots S t).mpr ⟨c, v, se⟩
  · intro equal
    exact absent (equal.symm ▸ (mem_roots S i).mpr ⟨a, j, eq⟩)

def compose {k m : Nat} (T U : Presentation k m) : Presentation k m where
  equations := U.equations
  reconstruct := fun i => substitute U.reconstruct (T.reconstruct i)
  project := fun i => substitute T.project (U.project i)

theorem compose_correct {k m : Nat} (S : System k m) (T U : Presentation k m)
    (ht : Correct S T) (hu : Correct T.equations U) : Correct S (compose T U) := by
  intro p
  constructor
  · intro v sat
    obtain ⟨st, bt⟩ := (ht p).1 v sat
    obtain ⟨su, bu⟩ := (hu p).1 _ st
    refine ⟨?_, ?_⟩
    · simpa only [compose, map_compose] using su
    · simp only [compose, map_compose, bu, bt]
  · intro w sat
    obtain ⟨su, bu⟩ := (hu p).2 w sat
    obtain ⟨st, bt⟩ := (ht p).2 _ su
    refine ⟨?_, ?_⟩
    · simpa only [compose, map_compose] using st
    · simp only [compose, map_compose, bt, bu]

/-- Every finite optional-definition system admits pair-guarded root-link
normalization with inverse solution maps and all original reconstructions.
No guardedness or solution oracle is assumed of the input system. -/
theorem root_link_normalization {k m : Nat} (S : System k m) :
    ∃ T : Presentation k m, Guarded T.equations ∧ Correct S T := by
  classical
  suffices ∀ n (S : System k m), (roots S).card = n →
      ∃ T : Presentation k m, Guarded T.equations ∧ Correct S T from
    this _ S rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S count
    by_cases guarded : Guarded S
    · refine ⟨⟨S, identity, identity⟩, guarded, ?_⟩
      intro p
      constructor <;> intro v sat <;> exact ⟨sat, rfl⟩
    · obtain ⟨i, a, j, eq⟩ : ∃ i a j, S i = some (.var a j) := by
        simpa only [Guarded, not_forall, not_not] using guarded
      by_cases ji : j = i
      · subst j
        obtain ⟨U, gu, cu⟩ := ih _ (count ▸ selfStep_decreases S i a eq)
          (selfStep S i a).equations rfl
        exact ⟨compose (selfStep S i a) U, gu,
          compose_correct S _ _ (selfStep_correct S i a eq) cu⟩
      · obtain ⟨U, gu, cu⟩ := ih _ (count ▸ linkStep_decreases S i a j eq)
          (linkStep S i a j).equations rfl
        exact ⟨compose (linkStep S i a j) U, gu,
          compose_correct S _ _ (linkStep_correct S i a j ji eq) cu⟩

open NativeGuardedImageSaturation

/-- The presentation is selected from the proved normalization construction. -/
noncomputable def normalForm {k m : Nat} (S : System k m) : Presentation k m :=
  Classical.choose (root_link_normalization S)

private theorem normalForm_guarded {k m : Nat} (S : System k m) :
    Guarded (normalForm S).equations := (Classical.choose_spec (root_link_normalization S)).1

private theorem normalForm_correct {k m : Nat} (S : System k m) :
    Correct S (normalForm S) := (Classical.choose_spec (root_link_normalization S)).2

/-- Transform every filter occurrence through its original reconstruction;
the list order, repetitions and thresholds are retained. -/
def transformedFilters {k m : Nat} (T : Presentation k m) (filters : List (Filter k m)) :
    List (Filter k m) := filters.map fun f => (substitute T.reconstruct f.1, f.2)

private theorem filters_threshold {k m : Nat} (T : Presentation k m)
    (filters : List (Filter k m)) :
    threshold (transformedFilters T filters) = threshold filters := by
  simp only [threshold, transformedFilters, List.map_map, Function.comp_def]

theorem filters_correspond {k m : Nat} (T : Presentation k m)
    (p : Fin k → Nat) (w : Fin m → CompletionTree) (filters : List (Filter k m)) :
    Passes p w (transformedFilters T filters) ↔
      Passes p (mapValues p T.reconstruct w) filters := by
  constructor
  · intro pass E t ht
    have accepted := pass (substitute T.reconstruct E) t (List.mem_map.mpr ⟨(E, t), ht, rfl⟩)
    rwa [substitute_value] at accepted
  · intro pass E t ht
    obtain ⟨⟨F, u⟩, hf, eq⟩ := List.mem_map.mp ht
    cases eq
    rw [substitute_value]
    exact pass F u hf

/-- Modes are indexed only by the actual undefined normalized states.
Fixed ground slots introduced by elimination do not belong to this list. -/
abbrev FreeMode {k m : Nat} (S : System k m) (s : Nat) :=
  {i : Fin m // (normalForm S).equations i = none} → Option (Fin (s + 2))

noncomputable def totalMode {k m s : Nat} (S : System k m) (mode : FreeMode S s) :
    Mode s m := fun i => if h : (normalForm S).equations i = none then mode ⟨i, h⟩ else none

/-- The original mode is read on the exact projected normalized free list. -/
def OriginalInMode {k m s : Nat} (S : System k m) (p : Fin k → Nat)
    (mode : FreeMode S s) (v : Fin m → CompletionTree) : Prop :=
  InMode (normalForm S).equations s (totalMode S mode)
    (mapValues p (normalForm S).project v)

private noncomputable def filterMode {k m : Nat} (S : System k m)
    (filters : List (Filter k m)) (mode : FreeMode S (threshold filters)) :
    Mode (threshold (transformedFilters (normalForm S) filters)) m :=
  cast (congrArg (fun s => Mode s m) (filters_threshold (normalForm S) filters).symm)
    (totalMode S mode)

/-- Reconstruct all original names from the canonical normalized extension. -/
noncomputable def originalCanonical {k m : Nat} (S : System k m) (p : Fin k → Nat)
    (filters : List (Filter k m)) (mode : FreeMode S (threshold filters)) :
    Fin m → CompletionTree :=
  mapValues p (normalForm S).reconstruct
    (canonical (normalForm S).equations p (normalForm_guarded S) (filterMode S filters mode))

/-- NIS.15 on arbitrary original optional-definition systems: both solution
directions, all original names and every retained actual-image filter. -/
theorem original_saturation {k m : Nat} (S : System k m) (p : Fin k → Nat)
    (filters : List (Filter k m)) (mode : FreeMode S (threshold filters)) :
    Satisfies S p (originalCanonical S p filters mode) ∧
    OriginalInMode S p mode (originalCanonical S p filters mode) ∧
    ((∃ v, Satisfies S p v ∧ OriginalInMode S p mode v ∧ Passes p v filters) ↔
      Passes p (originalCanonical S p filters mode) filters) := by
  let T := normalForm S
  let K := canonical T.equations p (normalForm_guarded S) (filterMode S filters mode)
  have law := normalized_saturation T.equations p (normalForm_guarded S)
    (transformedFilters T filters) (filterMode S filters mode)
  have corr := normalForm_correct S p
  have back := corr.2 K law.1
  have mode_match (w : Fin m → CompletionTree) :
      InMode T.equations (threshold (transformedFilters T filters))
        (filterMode S filters mode) w ↔
      InMode T.equations (threshold filters) (totalMode S mode) w := by
    have transport (s t : Nat) (h : s = t) (md : Mode t m) :
        InMode T.equations s (cast (congrArg (fun a => Mode a m) h.symm) md) w ↔
          InMode T.equations t md w := by
      cases h
      rfl
    exact transport _ _ (filters_threshold T filters) (totalMode S mode)
  have km : InMode T.equations (threshold filters) (totalMode S mode) K :=
    (mode_match K).mp law.2.1
  refine ⟨back.1, ?_, ?_⟩
  · change InMode T.equations (threshold filters) (totalMode S mode)
      (mapValues p T.project (mapValues p T.reconstruct K))
    rw [back.2]
    exact km
  · constructor
    · rintro ⟨v, sat, vm, passes⟩
      have forward := corr.1 v sat
      have transformed : Passes p (mapValues p T.project v) (transformedFilters T filters) := by
        apply (filters_correspond T p _ filters).mpr
        rw [forward.2]
        exact passes
      have accepted := law.2.2.mp ⟨mapValues p T.project v, forward.1,
        (mode_match _).mpr vm, transformed⟩
      exact (filters_correspond T p K filters).mp accepted
    · intro passes
      refine ⟨originalCanonical S p filters mode, back.1, ?_, passes⟩
      change InMode T.equations (threshold filters) (totalMode S mode)
        (mapValues p T.project (mapValues p T.reconstruct K))
      rw [back.2]
      exact km

end D5.S3.Arith.FibonacciAtomic.Observer.NativeRootLinkNormalization
