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

private theorem shift_value {k m : Nat} (p : Fin k → Nat)
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

private theorem substitute_value {k m : Nat} (p : Fin k → Nat)
    (R : Fin m → Expression k m) (v : Fin m → CompletionTree) (E : Expression k m) :
    evaluate p v (substitute R E) = evaluate p (mapValues p R v) E := by
  induction E with
  | ground t => rfl
  | token j c => rfl
  | var a j => exact shift_value p v a (R j)
  | pair A B ihA ihB => exact congrArg₂ node ihA ihB

def identity {k m : Nat} : Fin m → Expression k m := fun i => .var 0 i

private theorem map_identity {k m : Nat} (p : Fin k → Nat) (v : Fin m → CompletionTree) :
    mapValues p identity v = v := rfl

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

private def selfStep {k m : Nat} (S : System k m) (i : Fin m) (a : Nat) :
    Presentation k m where
  equations := Function.update S i (if a = 0 then none else some (.token (Fin.last k) 0))
  reconstruct := identity
  project := identity

private theorem selfStep_correct {k m : Nat} (S : System k m) (i : Fin m) (a : Nat)
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

private def linkStep {k m : Nat} (S : System k m) (i : Fin m) (a : Nat) (j : Fin m) :
    Presentation k m where
  equations := fun t => if t = i then some (.ground (.of true))
    else (S t).map (substitute (linkRecon i a j))
  reconstruct := linkRecon i a j
  project := linkProject i

private theorem linkStep_correct {k m : Nat} (S : System k m) (i : Fin m) (a : Nat)
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
      rw [project, if_neg ti, substitute_value, back]
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
    · rw [recon, if_neg ti, ← substitute_value]
      exact sat t _ (by simp only [linkStep, ti, ite_false, defn, Option.map_some])

private noncomputable def roots {k m : Nat} (S : System k m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i => ∃ a j, S i = some (.var a j)

private theorem mem_roots {k m : Nat} (S : System k m) (i : Fin m) :
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

private theorem selfStep_decreases {k m : Nat} (S : System k m) (i : Fin m) (a : Nat)
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

private theorem linkStep_decreases {k m : Nat} (S : System k m) (i : Fin m) (a : Nat)
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

private def compose {k m : Nat} (T U : Presentation k m) : Presentation k m where
  equations := U.equations
  reconstruct := fun i => substitute U.reconstruct (T.reconstruct i)
  project := fun i => substitute T.project (U.project i)

private theorem compose_correct {k m : Nat} (S : System k m) (T U : Presentation k m)
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

end D5.S3.Arith.FibonacciAtomic.Observer.NativeRootLinkNormalization
