/- GID: D5/S1/Words/ReturnWords/CoherentReturnPathTemplates
   generality: G
   mirror-B: D5/B/S1/Words/ReturnWords/CoherentReturnPathTemplates
   mirror-E: none(waiver:structural-word-proof)
   anchors: []
   utility: none
   digest: Synchronized labelled returns determine bounded component phases. -/

import D5.S1.Words.Powers.WordPower
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Combinatorics.Quiver.ConnectedComponent
import Mathlib.Combinatorics.Quiver.Path.Weight
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Combinatorics.Quiver.Path.Decomposition
import Mathlib.Data.Stream.Init
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic

namespace D5.S1.Words.ReturnWords.CoherentReturnPathTemplates

open Quiver D5.S1.Words.Powers

universe u v w

/-- Edge labels retain the actual arrow, including parallel arrows. -/
abbrev EdgeLabel (V : Type u) [Quiver.{v} V] (α : Type w) :=
  ∀ {a b : V}, (a ⟶ b) → α

/-- The output of a path is its free-monoid weight under singleton edge labels. -/
def output {V : Type u} [Quiver.{v} V] {α : Type w}
    (label : EdgeLabel V α) {a b : V} (H : Path a b) : List α :=
  (H.weight (fun e => FreeMonoid.of (label e))).toList

/-- The actual fiber of the native mutual-reachability quotient. -/
abbrev Component {V : Type u} [Quiver.{v} V] (S : StronglyConnectedComponent V) :=
  {a : V // StronglyConnectedComponent.mk a = S}

instance componentQuiver {V : Type u} [Quiver.{v} V]
    (S : StronglyConnectedComponent V) : Quiver.{v} (Component S) where
  Hom a b := a.val ⟶ b.val

/-- Inclusion keeps the ambient vertex and the actual arrow. -/
abbrev componentInclusion {V : Type u} [Quiver.{v} V]
    (S : StronglyConnectedComponent V) : Prefunctor (Component S) V where
  obj a := a.val
  map e := e

/-- An ambient path whose endpoints share an SCC lifts with every arrow intact.
Mutual reachability of the endpoints supplies the closing path used at each step. -/
noncomputable def liftComponentPath {V : Type u} [Quiver.{v} V]
    (S : StronglyConnectedComponent V) {a b : V} (H : Path a b)
    (ha : StronglyConnectedComponent.mk a = S)
    (hb : StronglyConnectedComponent.mk b = S) :
    {J : Path (⟨a, ha⟩ : Component S) (⟨b, hb⟩ : Component S) //
      (componentInclusion S).mapPath J = H} := by
  classical
  induction H with
  | nil => exact ⟨Path.nil, rfl⟩
  | @cons b c H e ih =>
    let back := ((StronglyConnectedComponent.mk_eq_mk.mp (hb.trans ha.symm)).1).some
    have hmid : StronglyConnectedComponent.mk b = S :=
      (StronglyConnectedComponent.mk_eq_mk.mpr
        ⟨⟨H⟩, ⟨e.toPath.comp back⟩⟩).symm.trans ha
    let J := ih hmid
    refine ⟨J.val.cons e, ?_⟩
    change ((componentInclusion S).mapPath J.val).cons e = H.cons e
    rw [J.property]

/-- Restrict labels to all arrows between vertices in a component. -/
def componentLabel {V : Type u} [Quiver.{v} V] {α : Type w}
    (label : EdgeLabel V α) (S : StronglyConnectedComponent V) :
    EdgeLabel (Component S) α := fun e => label e

/-- Component inclusion preserves the length of every internal path. -/
theorem component_inclusion_length {V : Type u} [Quiver.{v} V]
    (S : StronglyConnectedComponent V) {a b : Component S}
    (H : Path a b) : ((componentInclusion S).mapPath H).length = H.length := by
  induction H with
  | nil => rfl
  | cons H e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]
/-- Component inclusion preserves path output under the restricted edge labels. -/
theorem component_inclusion_output {V : Type u} [Quiver.{v} V] {α : Type w}
    (label : EdgeLabel V α) (S : StronglyConnectedComponent V) {a b : Component S}
    (H : Path a b) : output label ((componentInclusion S).mapPath H) =
      output (componentLabel label S) H := by
  induction H with
  | nil => simp [output]
  | cons H e ih =>
    simp only [Prefunctor.mapPath_cons, output, Path.weight_cons, FreeMonoid.toList_mul,
      FreeMonoid.toList_of] at ih ⊢
    rw [ih]; rfl

/-- Cyclicity is witnessed by an actual positive internal return path. -/
def Cyclic {V : Type u} [Quiver.{v} V] (S : StronglyConnectedComponent V) : Prop :=
  ∃ q : Component S, ∃ C : Path q q, 0 < C.length

/-- The exact least-common-multiple synchronization equation at a basepoint. -/
def SynchronizedAt {V : Type u} [Quiver.{v} V] {α : Type w}
    (label : EdgeLabel V α) (q : V) : Prop :=
  ∀ (A B : Path q q), 0 < A.length → 0 < B.length →
    wordPower (Nat.lcm A.length B.length / A.length) (output label A) =
      wordPower (Nat.lcm A.length B.length / B.length) (output label B)

/-- Coherence asserts synchronization at some actual component vertex. -/
def Coherent {V : Type u} [Quiver.{v} V] {α : Type w}
    (label : EdgeLabel V α) (S : StronglyConnectedComponent V) : Prop :=
  ∃ q : Component S, SynchronizedAt (componentLabel label S) q

/-- A nonzero cyclic block and phase satisfying the laws on every internal arrow.
The function on residues is exactly a word of length `p`. -/
def BoundedPhases {V : Type u} [Quiver.{v} V] {α : Type w}
    (label : EdgeLabel V α) (S : StronglyConnectedComponent V) : Prop :=
  ∃ p : Nat, 0 < p ∧ p ≤ Nat.card (Component S) ∧
    ∃ P : ZMod p → α, ∃ θ : Component S → ZMod p,
      ∀ {a b : Component S} (e : a ⟶ b),
        componentLabel label S e = P (θ a) ∧ θ b = θ a + 1

/-- Each entry chooses one positive purely periodic stream before all finite paths.
Indexing by `Option` includes empty paths without choosing a default letter. -/
def PeriodicPrefixes {V : Type u} [Quiver.{v} V] {α : Type w}
    (label : EdgeLabel V α) (S : StronglyConnectedComponent V) : Prop :=
  ∀ a : Component S, ∃ X : Stream' α, ∃ p : Nat, 0 < p ∧
    (∀ n, X (n + p) = X n) ∧
    ∀ {b : Component S} (H : Path a b) (i : Nat), i < H.length →
      (output (componentLabel label S) H)[i]? = some (X i)

/-- Concatenation powers of an actual return, retaining all of its arrows. -/
def returnPower {V : Type u} [Quiver.{v} V] {q : V} (A : Path q q) : Nat → Path q q
  | 0 => Path.nil
  | k + 1 => A.comp (returnPower A k)

/-- A template is a sequence of power/literal segments. An empty power block denotes
only a literal segment; all counted power factors therefore have positive length. -/
abbrev PowerTemplate (α : Type w) := List (List α × List α)

/-- Realize fixed template blocks with a chosen tuple of nonnegative exponents. -/
def templateOutput {α : Type w} : PowerTemplate α → (Nat → Nat) → List α
  | [], _ => []
  | (P, a) :: t, k => wordPower (k 0) P ++ a ++ templateOutput t (fun i => k (i + 1))

/-- Literal-only segments do not count as periodic factors. -/
noncomputable def factorCount {α : Type w} (t : PowerTemplate α) : Nat := by
  classical
  exact (t.filter fun part => part.1 ≠ []).length

/-- The actual distinct SCCs visited by a path. -/
noncomputable def visitedComponents {V : Type u} [Quiver.{v} V] {a b : V}
    (H : Path a b) : Finset (StronglyConnectedComponent V) := by
  classical
  exact (H.vertices.map StronglyConnectedComponent.mk).toFinset

/-- Cyclic SCCs visited by this very path. -/
noncomputable def visitedCyclicCount {V : Type u} [Quiver.{v} V] {a b : V}
    (H : Path a b) : Nat := by
  classical
  exact ((visitedComponents H).filter Cyclic).card

/-- One finite template family, chosen before paths, covers all outputs. The statement
is a cover and places no realizability requirement on independently chosen exponents. -/
def FiniteTemplateCover {V : Type u} [Quiver.{v} V] {α : Type w}
    (label : EdgeLabel V α) : Prop :=
  ∃ T : Set (PowerTemplate α), T.Finite ∧
    ∀ {a b : V} (H : Path a b), ∃ t ∈ T, ∃ k : Nat → Nat,
      output label H = templateOutput t k ∧ factorCount t ≤ visitedCyclicCount H

/-- The two vertices of the source's multiple-component example. -/
inductive TwoLoopVertex
  | left
  | right
  deriving DecidableEq

instance : Fintype TwoLoopVertex where
  elems := {.left, .right}
  complete x := by cases x <;> simp

/-- The two loops and the one directed connecting arrow. -/
inductive TwoLoopArrow : TwoLoopVertex → TwoLoopVertex → Type
  | leftLoop : TwoLoopArrow .left .left
  | rightLoop : TwoLoopArrow .right .right
  | bridge : TwoLoopArrow .left .right

instance : Quiver TwoLoopVertex where
  Hom := TwoLoopArrow

/-- The three different symbols are the two loop labels and the connecting label. -/
def twoLoopLabel : EdgeLabel TwoLoopVertex (Fin 3)
  | _, _, .leftLoop => 0
  | _, _, .rightLoop => 1
  | _, _, .bridge => 2

/-- An actual crossing path, with independently chosen counts in the two SCCs. -/
def twoLoopCrossing (i j : Nat) : Path TwoLoopVertex.left TwoLoopVertex.right :=
  (returnPower (@Quiver.Hom.toPath TwoLoopVertex _ .left .left TwoLoopArrow.leftLoop) i).comp
    ((@Quiver.Hom.toPath TwoLoopVertex _ .left .right TwoLoopArrow.bridge).comp
      (returnPower (@Quiver.Hom.toPath TwoLoopVertex _ .right .right
        TwoLoopArrow.rightLoop) j))

/-- The crossing output `a^i c b^j` over three different symbols. -/
def twoLoopWord (i j : Nat) : List (Fin 3) :=
  wordPower i [0] ++ [2] ++ wordPower j [1]

/-- A fixed single-power template; an empty block permits a finite literal exception. -/
structure SinglePowerTemplate (α : Type w) where
  before : List α
  block : List α
  after : List α

/-- One single-power template at one nonnegative exponent. -/
def singlePowerOutput {α : Type w} (t : SinglePowerTemplate α) (k : Nat) : List α :=
  t.before ++ wordPower k t.block ++ t.after

/-- The two coherent cyclic SCCs exhibit unbounded fixed-length output counts and
cannot be covered by any fixed finite family of single-power templates. -/
def TwoLoopBoundary : Prop :=
  (StronglyConnectedComponent.mk TwoLoopVertex.left ≠
    StronglyConnectedComponent.mk TwoLoopVertex.right) ∧
  Cyclic (StronglyConnectedComponent.mk TwoLoopVertex.left) ∧
  Cyclic (StronglyConnectedComponent.mk TwoLoopVertex.right) ∧
  (∀ S : StronglyConnectedComponent TwoLoopVertex, Cyclic S → Coherent twoLoopLabel S) ∧
  (∀ i j, output twoLoopLabel (twoLoopCrossing i j) = twoLoopWord i j) ∧
  (∀ n, Function.Injective (fun i : Fin (n + 1) => twoLoopWord i.val (n - i.val)) ∧
    ∀ i : Fin (n + 1), (twoLoopWord i.val (n - i.val)).length = n + 1) ∧
  ¬ ∃ T : Set (SinglePowerTemplate (Fin 3)), T.Finite ∧
    ∀ i j, ∃ t ∈ T, ∃ k : Nat, twoLoopWord i j = singlePowerOutput t k

/-- LCM-synchronized actual returns construct bounded phases, and these are equivalent
to periodic output prefixes at every entry. The synchronized-return law then holds
at every vertex, without identifying paths that have equal outputs. -/
theorem coherent_component_phases {V : Type u} [Quiver.{v} V] [Finite V]
    {α : Type w} (label : EdgeLabel V α) (S : StronglyConnectedComponent V)
    (hcyclic : Cyclic S) :
    (Coherent label S ↔ BoundedPhases label S) ∧
    (BoundedPhases label S ↔ PeriodicPrefixes label S) ∧
    (Coherent label S →
      ∀ q : Component S, SynchronizedAt (componentLabel label S) q) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let W := Component S
  let ℓ : EdgeLabel W α := componentLabel label S
  have outnil (a : W) : output ℓ (Path.nil : Path a a) = [] := by simp [output]
  have outcons {a b c : W} (H : Path a b) (e : b ⟶ c) :
      output ℓ (H.cons e) = output ℓ H ++ [ℓ e] := by
    simp only [output, Path.weight_cons, FreeMonoid.toList_mul,
      FreeMonoid.of, FreeMonoid.toList_ofList]
  have outcomp {a b c : W} (H : Path a b) (J : Path b c) :
      output ℓ (H.comp J) = output ℓ H ++ output ℓ J := by
    exact congrArg FreeMonoid.toList (Path.weight_comp _ H J)
  have outlen {a b : W} (H : Path a b) : (output ℓ H).length = H.length := by
    induction H with
    | nil => rw [outnil]; rfl
    | cons H e ih => simp only [outcons, List.length_append, List.length_singleton,
        Path.length_cons, ih]
  have powlen {q : W} (A : Path q q) (k : Nat) :
      (returnPower A k).length = k * A.length := by
    induction k with
    | zero => simp [returnPower]
    | succ k ih => simp only [returnPower, Path.length_comp, ih, Nat.succ_mul]; omega
  have powout {q : W} (A : Path q q) (k : Nat) :
      output ℓ (returnPower A k) = wordPower k (output ℓ A) := by
    induction k with
    | zero => simp [returnPower, outnil]
    | succ k ih => rw [returnPower, outcomp, ih, wordPower_succ]
  have connected : Quiver.IsStronglyConnected W := by
    intro a b
    obtain ⟨H⟩ := (StronglyConnectedComponent.mk_eq_mk.mp
      (a.property.trans b.property.symm)).1
    exact ⟨(liftComponentPath S H a.property b.property).val⟩
  have positive (q : W) : ∃ C : Path q q, 0 < C.length := by
    obtain ⟨r, C, hC⟩ := hcyclic
    obtain ⟨A⟩ := connected q r
    obtain ⟨B⟩ := connected r q
    refine ⟨A.comp (C.comp B), ?_⟩
    simp only [Path.length_comp]
    omega
  have prefix_to_sync (hF : PeriodicPrefixes label S) :
      ∀ q : W, SynchronizedAt ℓ q := by
    intro q A B hA hB
    obtain ⟨X, p, hp, hperiod, hprefix⟩ := hF q
    let L := Nat.lcm A.length B.length
    have hLA : L / A.length * A.length = L :=
      Nat.div_mul_cancel (Nat.dvd_lcm_left _ _)
    have hLB : L / B.length * B.length = L :=
      Nat.div_mul_cancel (Nat.dvd_lcm_right _ _)
    have hlenA : (wordPower (L / A.length) (output ℓ A)).length = L := by
      rw [length_wordPower, outlen, hLA]
    have hlenB : (wordPower (L / B.length) (output ℓ B)).length = L := by
      rw [length_wordPower, outlen, hLB]
    apply List.ext_getElem?
    intro i
    by_cases hi : i < L
    · rw [← powout, ← powout]
      exact (hprefix (returnPower A (L / A.length)) i
        (by rw [powlen, hLA]; exact hi)).trans
        (hprefix (returnPower B (L / B.length)) i
          (by rw [powlen, hLB]; exact hi)).symm
    · change (wordPower (L / A.length) (output ℓ A))[i]? =
        (wordPower (L / B.length) (output ℓ B))[i]?
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  have phases_to_prefix (hP : BoundedPhases label S) : PeriodicPrefixes label S := by
    obtain ⟨p, hp, hbound, P, θ, hedge⟩ := hP
    have pathlaw {a b : W} (H : Path a b) :
        θ b = θ a + (H.length : ZMod p) ∧
        ∀ i, i < H.length → (output ℓ H)[i]? = some (P (θ a + (i : ZMod p))) := by
      induction H with
      | nil => exact ⟨by simp, by simp⟩
      | @cons b c H e ih =>
        obtain ⟨he, hθ⟩ := hedge e
        refine ⟨?_, ?_⟩
        · rw [hθ, ih.1, Path.length_cons, Nat.cast_add, Nat.cast_one, add_assoc]
        · intro i hi
          rw [outcons]
          by_cases hiH : i < H.length
          · rw [List.getElem?_append_left (by rw [outlen]; exact hiH)]
            exact ih.2 i hiH
          · have hieq : i = H.length := by simp only [Path.length_cons] at hi; omega
            subst i
            rw [List.getElem?_append_right (by rw [outlen]), outlen, Nat.sub_self]
            change some (ℓ e) = _
            change ℓ e = P (θ b) at he
            rw [he, ih.1]
    intro a
    refine ⟨fun n => P (θ a + (n : ZMod p)), p, hp, ?_, ?_⟩
    · intro n
      simp only [Nat.cast_add, ZMod.natCast_self, add_zero]
    · intro b H i hi
      exact (pathlaw H).2 i hi
  have sync_to_phases (hC : Coherent label S) : BoundedPhases label S := by
    obtain ⟨q, hsync⟩ := hC
    obtain ⟨C, hCpos⟩ := positive q
    let X : Stream' (Option α) := fun n => (output ℓ C)[n % C.length]?
    let shift : Stream' (Option α) → Stream' (Option α) := fun Y n => Y (n + 1)
    have shift_iter (Y : Stream' (Option α)) (k n : Nat) :
        (shift^[k] Y) n = Y (n + k) := by
      induction k generalizing n with
      | zero => simp
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        change (shift^[k] Y) (n + 1) = _
        rw [ih]; congr 1; omega
    have common (A : Path q q) (hA : 0 < A.length) (n : Nat) :
        X n = (output ℓ A)[n % A.length]? := by
      let L := Nat.lcm A.length C.length
      have hL : 0 < L := Nat.lcm_pos hA hCpos
      have ht : n % L < L := Nat.mod_lt _ hL
      have hLA : L / A.length * (output ℓ A).length = L := by
        rw [outlen]; exact Nat.div_mul_cancel (Nat.dvd_lcm_left _ _)
      have hLC : L / C.length * (output ℓ C).length = L := by
        rw [outlen]; exact Nat.div_mul_cancel (Nat.dvd_lcm_right _ _)
      have heq := congrArg (fun U : List α => U[n % L]?) (hsync A C hA hCpos)
      rw [wordPower_getElem? _ _ _ (by rw [hLA]; exact ht),
        wordPower_getElem? _ _ _ (by rw [hLC]; exact ht), outlen, outlen,
        Nat.mod_mod_of_dvd _ (Nat.dvd_lcm_left _ _),
        Nat.mod_mod_of_dvd _ (Nat.dvd_lcm_right _ _)] at heq
      exact heq.symm
    have return_period (A : Path q q) (hA : 0 < A.length) :
        Function.IsPeriodicPt shift A.length X := by
      funext n
      rw [shift_iter, common A hA, common A hA, Nat.add_mod_right]
    let p := Function.minimalPeriod shift X
    have hp : 0 < p := (return_period C hCpos).minimalPeriod_pos hCpos
    have hple : p ≤ C.length := (return_period C hCpos).minimalPeriod_le hCpos
    have period : ∀ n, X (n + p) = X n := by
      intro n
      exact (shift_iter X p n).symm.trans
        (congrFun (Function.isPeriodicPt_minimalPeriod shift X) n)
    have modX (n : Nat) : X (n % p) = X n := by
      have h := congrFun (Function.iterate_mod_minimalPeriod_eq (f := shift) (x := X)
        (n := n)) 0
      simpa only [shift_iter, Nat.zero_add] using h
    have retdiv (A : Path q q) : p ∣ A.length := by
      by_cases hA : 0 < A.length
      · exact (return_period A hA).minimalPeriod_dvd
      · have : A.length = 0 := by omega
        rw [this]; exact dvd_zero p
    have retprefix (A : Path q q) (i : Nat) (hi : i < A.length) :
        (output ℓ A)[i]? = X i := by
      have hA : 0 < A.length := by omega
      simpa only [Nat.mod_eq_of_lt hi] using (common A hA i).symm
    let toq (a : W) : Path a q := (connected a q).some
    let fromq (a : W) : Path q a := (connected q a).some
    let θ : W → ZMod p := fun a => ((fromq a).length : ZMod p)
    have phase_independent {a : W} (H : Path q a) :
        (H.length : ZMod p) = θ a := by
      have hH : ((H.comp (toq a)).length : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr (retdiv _)
      have hQ : (((fromq a).comp (toq a)).length : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr (retdiv _)
      simp only [Path.length_comp, Nat.cast_add] at hH hQ
      exact add_right_cancel (hH.trans hQ.symm)
    have hθq : θ q = 0 := by
      simpa using (phase_independent (Path.nil : Path q q)).symm
    let : NeZero p := ⟨hp.ne'⟩
    have letters (z : ZMod p) : ∃ a : α, X z.val = some a := by
      have hz : z.val < C.length := (ZMod.val_lt z).trans_le hple
      dsimp only [X]
      rw [Nat.mod_eq_of_lt hz]
      exact ⟨(output ℓ C)[z.val]'(by rw [outlen]; exact hz),
        List.getElem?_eq_getElem (by rw [outlen]; exact hz)⟩
    let P : ZMod p → α := fun z => (letters z).choose
    have Plaw (n : Nat) : some (P (n : ZMod p)) = X n := by
      rw [← modX n]
      exact (letters (n : ZMod p)).choose_spec.symm.trans
        (congrArg X (ZMod.val_natCast p n))
    have edges {a b : W} (e : a ⟶ b) : ℓ e = P (θ a) ∧ θ b = θ a + 1 := by
      have hphase := phase_independent ((fromq a).cons e)
      have hinc : θ b = θ a + 1 := by
        simpa only [Path.length_cons, Nat.cast_add, Nat.cast_one] using hphase.symm
      refine ⟨?_, hinc⟩
      let R := ((fromq a).cons e).comp (toq b)
      have hi : (fromq a).length < R.length := by
        dsimp only [R]; simp only [Path.length_comp, Path.length_cons]; omega
      have hchar := retprefix R (fromq a).length hi
      rw [outcomp, List.getElem?_append_left (by rw [outlen, Path.length_cons]; omega),
        outcons, List.getElem?_append_right (by rw [outlen]), outlen, Nat.sub_self] at hchar
      simp only [List.getElem?_cons_zero] at hchar
      exact Option.some.inj (hchar.trans (Plaw (fromq a).length).symm)
    have surj : Function.Surjective θ := by
      intro z
      obtain ⟨a, H, J, hCJ, hlen⟩ := C.exists_eq_comp_of_le_length
        ((ZMod.val_lt z).le.trans hple)
      refine ⟨a, ?_⟩
      rw [← phase_independent H, hlen, ZMod.natCast_zmod_val]
    have hbound : p ≤ Nat.card W := by
      let : Fintype W := Fintype.ofFinite W
      simpa only [ZMod.card, Nat.card_eq_fintype_card] using
        Fintype.card_le_of_surjective θ surj
    exact ⟨p, hp, hbound, P, θ, edges⟩
  have CtoF : Coherent label S → PeriodicPrefixes label S :=
    fun h => phases_to_prefix (sync_to_phases h)
  have FtoC : PeriodicPrefixes label S → Coherent label S := by
    intro hF
    obtain ⟨q, C, hC⟩ := hcyclic
    exact ⟨q, prefix_to_sync hF q⟩
  exact ⟨⟨sync_to_phases, fun h => FtoC (phases_to_prefix h)⟩,
    ⟨phases_to_prefix, fun h => sync_to_phases (FtoC h)⟩,
    fun h => prefix_to_sync (CtoF h)⟩

/-- The complete local characterization and cross-component finite cover, together
with the two-loop obstruction to a finite single-power replacement. Equal output
words impose no equality on actual paths, arrows, or separately observed histories. -/
theorem result {V : Type u} [Quiver.{v} V] [Finite V]
    {α : Type w} [Finite α] (label : EdgeLabel V α) :
    (∀ S : StronglyConnectedComponent V, Cyclic S →
      (Coherent label S ↔ BoundedPhases label S) ∧
      (BoundedPhases label S ↔ PeriodicPrefixes label S) ∧
      (Coherent label S →
        ∀ q : Component S, SynchronizedAt (componentLabel label S) q)) ∧
    ((∀ S : StronglyConnectedComponent V, Cyclic S → Coherent label S) →
      FiniteTemplateCover label) ∧ TwoLoopBoundary := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let : Fintype α := Fintype.ofFinite α
  refine ⟨fun S hc => coherent_component_phases label S hc, ?_, ?_⟩
  · intro hcoherent
    let n := Fintype.card V
    let sc := StronglyConnectedComponent.mk (V := V)
    have outnil (a : V) : output label (Path.nil : Path a a) = [] := by simp [output]
    have outcons {a b c : V} (H : Path a b) (e : b ⟶ c) :
        output label (H.cons e) = output label H ++ [label e] := by
      simp only [output, Path.weight_cons, FreeMonoid.toList_mul, FreeMonoid.toList_of]
    have outcomp {a b c : V} (H : Path a b) (J : Path b c) :
        output label (H.comp J) = output label H ++ output label J :=
      congrArg FreeMonoid.toList (Path.weight_comp _ H J)
    have outlen {a b : V} (H : Path a b) : (output label H).length = H.length := by
      induction H with
      | nil => rw [outnil]; rfl
      | cons H e ih => rw [outcons, List.length_append, ih]; rfl
    have mapvertices (S : StronglyConnectedComponent V) {a b : Component S}
        (H : Path a b) : ((componentInclusion S).mapPath H).vertices =
          H.vertices.map Subtype.val := by
      induction H with
      | nil => rfl
      | cons H e ih => simp only [Prefunctor.mapPath_cons, Path.vertices_cons,
          List.concat_eq_append, List.map_append, List.map_cons, List.map_nil, ih]
    have samevertices {a b : V} (H : Path a b) (hab : sc a = sc b) :
        ∀ x ∈ H.vertices, sc x = sc a := by
      let J := liftComponentPath (sc a) H rfl hab.symm
      intro x hx
      rw [← J.property, mapvertices] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact y.property
    have vnil (a : V) : visitedComponents (Path.nil : Path a a) = {sc a} := by
      simp [visitedComponents, sc]
    have vcons {a b c : V} (H : Path a b) (e : b ⟶ c) :
        visitedComponents (H.cons e) = insert (sc c) (visitedComponents H) := by
      simp [visitedComponents, Path.vertices_cons, List.concat_eq_append, sc]
    have vend {a b : V} (H : Path a b) : sc b ∈ visitedComponents H := by
      simp only [visitedComponents, List.mem_toFinset, List.mem_map]
      exact ⟨b, H.end_mem_vertices, rfl⟩
    have vcomp {a b c : V} (H : Path a b) (J : Path b c) :
        visitedComponents (H.comp J) = visitedComponents H ∪ visitedComponents J := by
      induction J with
      | nil =>
        rw [Path.comp_nil, vnil, Finset.union_singleton]
        exact (Finset.insert_eq_of_mem (vend H)).symm
      | cons J e ih => rw [Path.comp_cons, vcons, vcons, ih, Finset.union_insert]
    have vsame {a b : V} (H : Path a b) (hab : sc a = sc b) :
        visitedComponents H = {sc a} := by
      ext s
      simp only [visitedComponents, List.mem_toFinset, List.mem_map, Finset.mem_singleton]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact samevertices H hab x hx
      · rintro rfl; exact ⟨a, H.start_mem_vertices, rfl⟩
    let : Finite (StronglyConnectedComponent V) :=
      inferInstanceAs (Finite (Quotient (Quiver.stronglyConnectedSetoid V)))
    let : Fintype (StronglyConnectedComponent V) := Fintype.ofFinite _
    have componentbound (S : StronglyConnectedComponent V) : Nat.card (Component S) ≤ n := by
      simpa only [Nat.card_eq_fintype_card] using
        Fintype.card_le_of_injective (fun a : Component S => a.val) Subtype.val_injective
    have visitedbound {a b : V} (H : Path a b) : (visitedComponents H).card ≤ n := by
      refine (Finset.card_le_univ _).trans ?_
      apply Fintype.card_le_of_surjective sc
      intro S
      refine Quotient.inductionOn S (fun a => ?_)
      exact ⟨a, rfl⟩
    have run {a b : V} (H : Path a b) (hab : sc a = sc b) :
        ∃ P r : List α, ∃ k : Nat,
          output label H = wordPower k P ++ r ∧ P.length ≤ n ∧ r.length ≤ n ∧
          (P ≠ [] → Cyclic (sc a)) := by
      let S := sc a
      let J := liftComponentPath S H rfl hab.symm
      have hJlen : J.val.length = H.length := by rw [← component_inclusion_length S J.val, J.property]
      have hJout : output (componentLabel label S) J.val = output label H := by
        rw [← component_inclusion_output label S J.val, J.property]
      by_cases hc : Cyclic S
      · obtain ⟨p, hp, hps, B, θ, hedge⟩ :=
          (coherent_component_phases label S hc).1.mp (hcoherent S hc)
        have hpn : p ≤ n := hps.trans (componentbound S)
        have pathlaw {x y : Component S} (K : Path x y) :
            θ y = θ x + (K.length : ZMod p) ∧
            ∀ i, i < K.length → (output (componentLabel label S) K)[i]? =
              some (B (θ x + (i : ZMod p))) := by
          induction K with
          | nil => exact ⟨by simp, by simp [output]⟩
          | @cons y z K e ih =>
            obtain ⟨he, hθ⟩ := hedge e
            have hlength : (output (componentLabel label S) K).length = K.length := by
              rw [← component_inclusion_output label S K, outlen, component_inclusion_length]
            refine ⟨?_, ?_⟩
            · rw [hθ, ih.1, Path.length_cons, Nat.cast_add, Nat.cast_one, add_assoc]
            · intro i hi
              simp only [output, Path.weight_cons, FreeMonoid.toList_mul,
                FreeMonoid.toList_of]
              change (output (componentLabel label S) K ++ [componentLabel label S e])[i]? = _
              by_cases hiK : i < K.length
              · rw [List.getElem?_append_left (by omega)]
                exact ih.2 i hiK
              · have hieq : i = K.length := by simp only [Path.length_cons] at hi; omega
                subst i
                rw [List.getElem?_append_right (by omega), hlength, Nat.sub_self]
                simp only [List.getElem?_cons_zero, he, ih.1]
        let P : List α := List.ofFn fun i : Fin p => B (θ ⟨a, rfl⟩ + (i.val : ZMod p))
        let r : List α := List.ofFn fun i : Fin (H.length % p) =>
          B (θ ⟨a, rfl⟩ + (i.val : ZMod p))
        let k := H.length / p
        have Plen : P.length = p := List.length_ofFn
        have rlen : r.length = H.length % p := List.length_ofFn
        have total : (wordPower k P ++ r).length = H.length := by
          rw [List.length_append, length_wordPower, Plen, rlen]
          exact Nat.div_add_mod' H.length p
        refine ⟨P, r, k, ?_, by omega, by have := Nat.mod_lt H.length hp; omega,
          fun _ => hc⟩
        apply List.ext_getElem?
        intro i
        by_cases hi : i < H.length
        · rw [← hJout, (pathlaw J.val).2 i (by omega)]
          have hmod : (i % p : ZMod p) = (i : ZMod p) :=
            (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (Nat.mod_mod _ _)
          by_cases hik : i < k * p
          · rw [List.getElem?_append_left (by rw [length_wordPower, Plen]; exact hik),
              wordPower_getElem? _ _ _ (by rw [Plen]; exact hik), Plen]
            rw [List.getElem?_eq_getElem (by rw [Plen]; exact Nat.mod_lt _ hp)]
            simp only [P, List.getElem_ofFn, hmod]
          · have hle : k * p ≤ i := by omega
            rw [List.getElem?_append_right (by rw [length_wordPower, Plen]; exact hle),
              length_wordPower, Plen]
            have hir : i - k * p < H.length % p := by
              have hdiv : k * p + H.length % p = H.length := Nat.div_add_mod' H.length p
              omega
            rw [List.getElem?_eq_getElem (by rw [rlen]; exact hir)]
            have hcast : ((i - k * p : Nat) : ZMod p) = (i : ZMod p) := by
              rw [Nat.cast_sub hle, Nat.cast_mul, ZMod.natCast_self, mul_zero, sub_zero]
            simp only [r, List.getElem_ofFn, hcast]
        · rw [List.getElem?_eq_none (by rw [outlen]; omega),
            List.getElem?_eq_none (by rw [total]; omega)]
      · have hzero : H.length = 0 := by
          by_contra hne
          obtain ⟨back⟩ := (StronglyConnectedComponent.mk_eq_mk.mp hab).2
          let K := liftComponentPath S back hab.symm rfl
          apply hc
          refine ⟨⟨a, rfl⟩, J.val.comp K.val, ?_⟩
          rw [Path.length_comp, hJlen]; omega
        refine ⟨[], [], 0, ?_, by simp, by simp, by simp⟩
        have hlen := outlen H
        have hnil : output label H = [] := List.length_eq_zero_iff.mp (hlen.trans hzero)
        simp [hnil]
    have construct : ∀ {a b : V} (H : Path a b), ∃ t : PowerTemplate α, ∃ k : Nat → Nat,
        output label H = templateOutput t k ∧
        t.length ≤ (visitedComponents H).card ∧
        (∀ part ∈ t, part.1.length ≤ n + 1 ∧ part.2.length ≤ n + 1) ∧
        factorCount t ≤ visitedCyclicCount H := by
      intro a b H
      induction hlen : H.length using Nat.strong_induction_on generalizing a b with
      | h m ih =>
        by_cases hab : sc a = sc b
        · obtain ⟨P, r, k, hout, hP, hr, hcy⟩ := run H hab
          refine ⟨[(P, r)], fun _ => k, ?_, ?_, ?_, ?_⟩
          · simpa [templateOutput] using hout
          · rw [vsame H hab]; simp
          · simp only [List.mem_singleton]
            intro part hpart
            subst part
            change P.length ≤ n + 1 ∧ r.length ≤ n + 1
            exact ⟨by omega, by omega⟩
          · rw [visitedCyclicCount, vsame H hab]
            by_cases hPn : P = []
            · simp [factorCount, hPn]
            · rw [Finset.filter_singleton, if_pos (hcy hPn)]
              simp [factorCount, hPn]
        · obtain ⟨u, hu, v, hv, e, A, B, hH⟩ :=
            H.exists_mem_notMem_hom_path_path_of_notMem_mem
              {x | sc x = sc a} rfl (fun h => hab h.symm)
          change sc u = sc a at hu
          change ¬ sc v = sc a at hv
          have hBlt : B.length < m := by
            rw [hH, Path.length_comp, Path.length_comp, Path.length_toPath] at hlen; omega
          obtain ⟨t, k, ht, htlen, htparts, htcount⟩ := ih B.length hBlt B rfl
          obtain ⟨P, r, j, hA, hP, hr, hcy⟩ := run A hu.symm
          have no_revisit : sc a ∉ visitedComponents B := by
            intro hm
            simp only [visitedComponents, List.mem_toFinset, List.mem_map] at hm
            obtain ⟨x, hx, hxa⟩ := hm
            obtain ⟨B₁, B₂, hB⟩ := B.exists_eq_comp_of_mem_vertices hx
            obtain ⟨back⟩ := (StronglyConnectedComponent.mk_eq_mk.mp hxa).1
            have hva : sc v = sc a := StronglyConnectedComponent.mk_eq_mk.mpr
              ⟨⟨B₁.comp back⟩, ⟨A.comp e.toPath⟩⟩
            exact hv hva
          have vH : visitedComponents H = insert (sc a) (visitedComponents B) := by
            rw [hH, vcomp, vcomp, vsame A hu.symm]
            have ve : visitedComponents e.toPath = {sc u, sc v} := by
              rw [show e.toPath = Path.nil.cons e from rfl, vcons, vnil]
              simp [Finset.pair_comm]
            rw [ve, hu]
            ext s
            simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro (h | ((h | h) | h))
              · exact Or.inl h
              · exact Or.inl h
              · subst s
                simp only [visitedComponents, List.mem_toFinset, List.mem_map]
                exact Or.inr ⟨v, B.start_mem_vertices, rfl⟩
              · exact Or.inr h
            · rintro (h | h)
              · exact Or.inl h
              · exact Or.inr (Or.inr h)
          refine ⟨(P, r ++ [label e]) :: t,
            fun i => if i = 0 then j else k (i - 1), ?_, ?_, ?_, ?_⟩
          · rw [hH, outcomp, outcomp]
            have oute : output label e.toPath = [label e] := by
              change output label (Path.nil.cons e) = _
              rw [outcons, outnil]; rfl
            rw [oute, hA, ht]
            simp only [templateOutput, Nat.add_eq_zero_iff, Nat.one_ne_zero,
              and_false, if_false, Nat.add_sub_cancel]
            simp only [List.append_assoc, ite_true]
          · simp only [List.length_cons]
            rw [vH, Finset.card_insert_of_notMem no_revisit]; omega
          · intro part hpart
            simp only [List.mem_cons] at hpart
            rcases hpart with rfl | hpart
            · refine ⟨?_, ?_⟩
              · change P.length ≤ n + 1; omega
              simp only [List.length_append, List.length_singleton]
              omega
            · exact htparts part hpart
          · rw [visitedCyclicCount, vH, Finset.filter_insert]
            by_cases hc : Cyclic (sc a)
            · rw [if_pos hc, Finset.card_insert_of_notMem (by
                intro h; exact no_revisit (Finset.mem_filter.mp h).1)]
              have hfac : factorCount ((P, r ++ [label e]) :: t) ≤ factorCount t + 1 := by
                by_cases hPnil : P = [] <;> simp [factorCount, hPnil]
              change factorCount t ≤ (Finset.filter Cyclic (visitedComponents B)).card at htcount
              omega
            · rw [if_neg hc]
              have hPn : P = [] := by by_contra h; exact hc (hcy h)
              simpa [factorCount, hPn, visitedCyclicCount] using htcount
    let SmallWord := {U : List α // U.length ≤ n + 1}
    let : Finite SmallWord := (List.finite_length_le α (n + 1)).to_subtype
    let SmallPair := SmallWord × SmallWord
    let encode : List SmallPair → PowerTemplate α :=
      List.map fun part => (part.1.val, part.2.val)
    let T := encode '' {ts : List SmallPair | ts.length ≤ n}
    refine ⟨T, (List.finite_length_le SmallPair n).image encode, ?_⟩
    intro a b H
    obtain ⟨t, k, ht, htlen, htparts, htcount⟩ := construct H
    have hencode : ∃ ts : List SmallPair, ts.length = t.length ∧ encode ts = t := by
      clear ht htlen htcount
      induction t with
      | nil => exact ⟨[], rfl, rfl⟩
      | cons part t ih =>
        have hp := htparts part (by simp)
        obtain ⟨ts, hlen, heq⟩ := ih (fun q hq => htparts q (by simp [hq]))
        exact ⟨(⟨part.1, hp.1⟩, ⟨part.2, hp.2⟩) :: ts,
          by simp [hlen], by simp [encode, heq]⟩
    obtain ⟨ts, hlen, heq⟩ := hencode
    exact ⟨t, ⟨ts, by dsimp; rw [hlen]; exact htlen.trans (visitedbound H), heq⟩,
      k, ht, htcount⟩
  · let rank : TwoLoopVertex → Nat := fun x => match x with | .left => 0 | .right => 1
    have reachrank {a b : TwoLoopVertex} (H : Path a b) : rank a ≤ rank b := by
      induction H with
      | nil => exact le_rfl
      | @cons b c H e ih =>
        have he : rank b ≤ rank c := by cases e <;> decide
        exact ih.trans he
    have sccinj {a b : TwoLoopVertex}
        (h : StronglyConnectedComponent.mk a = StronglyConnectedComponent.mk b) : a = b := by
      obtain ⟨⟨A⟩, ⟨B⟩⟩ := StronglyConnectedComponent.mk_eq_mk.mp h
      have ha := reachrank A
      have hb := reachrank B
      cases a <;> cases b <;> simp_all [rank]
    have separated : StronglyConnectedComponent.mk TwoLoopVertex.left ≠
        StronglyConnectedComponent.mk TwoLoopVertex.right := by
      intro h
      exact TwoLoopVertex.noConfusion (sccinj h)
    have leftcyclic : Cyclic (StronglyConnectedComponent.mk TwoLoopVertex.left) := by
      let q : Component (StronglyConnectedComponent.mk TwoLoopVertex.left) := ⟨.left, rfl⟩
      exact ⟨q, Path.nil.cons (TwoLoopArrow.leftLoop : q ⟶ q), by simp⟩
    have rightcyclic : Cyclic (StronglyConnectedComponent.mk TwoLoopVertex.right) := by
      let q : Component (StronglyConnectedComponent.mk TwoLoopVertex.right) := ⟨.right, rfl⟩
      exact ⟨q, Path.nil.cons (TwoLoopArrow.rightLoop : q ⟶ q), by simp⟩
    have coherent : ∀ S : StronglyConnectedComponent TwoLoopVertex,
        Cyclic S → Coherent twoLoopLabel S := by
      intro S hc
      obtain ⟨q, C, hC⟩ := hc
      let letter : TwoLoopVertex → Fin 3 := fun x => match x with | .left => 0 | .right => 1
      have eqbase (a : Component S) : a.val = q.val :=
        sccinj (a.property.trans q.property.symm)
      have hcard : 1 ≤ Nat.card (Component S) := by
        let : Nonempty (Component S) := ⟨q⟩
        exact Nat.succ_le_of_lt Nat.card_pos
      apply (coherent_component_phases twoLoopLabel S ⟨q, C, hC⟩).1.mpr
      refine ⟨1, by decide, hcard, fun _ => letter q.val, fun _ => 0, ?_⟩
      intro a b e
      have ha := eqbase a
      have hb := eqbase b
      refine ⟨?_, Subsingleton.elim _ _⟩
      change twoLoopLabel e = letter q.val
      rcases a with ⟨a, haS⟩
      rcases b with ⟨b, hbS⟩
      rcases q with ⟨q, hqS⟩
      change a = q at ha
      change b = q at hb
      subst a
      subst b
      cases q <;> cases e <;> rfl
    have outnil (a : TwoLoopVertex) : output twoLoopLabel (Path.nil : Path a a) = [] := by
      simp [output]
    have outcons {a b c : TwoLoopVertex} (H : Path a b) (e : b ⟶ c) :
        output twoLoopLabel (H.cons e) = output twoLoopLabel H ++ [twoLoopLabel e] := by
      simp only [output, Path.weight_cons, FreeMonoid.toList_mul, FreeMonoid.toList_of]
    have outcomp {a b c : TwoLoopVertex} (H : Path a b) (J : Path b c) :
        output twoLoopLabel (H.comp J) = output twoLoopLabel H ++ output twoLoopLabel J :=
      congrArg FreeMonoid.toList (Path.weight_comp _ H J)
    have powout {q : TwoLoopVertex} (A : Path q q) (k : Nat) :
        output twoLoopLabel (returnPower A k) = wordPower k (output twoLoopLabel A) := by
      induction k with
      | zero => simp [returnPower, outnil]
      | succ k ih => rw [returnPower, outcomp, ih, wordPower_succ]
    have crossing (i j : Nat) : output twoLoopLabel (twoLoopCrossing i j) = twoLoopWord i j := by
      simp only [twoLoopCrossing, outcomp, powout]
      have oa : output twoLoopLabel
          (@Quiver.Hom.toPath TwoLoopVertex _ .left .left TwoLoopArrow.leftLoop) = [0] := by
        change output twoLoopLabel (Path.nil.cons TwoLoopArrow.leftLoop) = _
        rw [outcons, outnil]; rfl
      have ob : output twoLoopLabel
          (@Quiver.Hom.toPath TwoLoopVertex _ .right .right TwoLoopArrow.rightLoop) = [1] := by
        change output twoLoopLabel (Path.nil.cons TwoLoopArrow.rightLoop) = _
        rw [outcons, outnil]; rfl
      have oc : output twoLoopLabel
          (@Quiver.Hom.toPath TwoLoopVertex _ .left .right TwoLoopArrow.bridge) = [2] := by
        change output twoLoopLabel (Path.nil.cons TwoLoopArrow.bridge) = _
        rw [outcons, outnil]; rfl
      rw [oa, ob, oc]
      simp only [twoLoopWord, List.append_assoc]
    have wlen (i j : Nat) : (twoLoopWord i j).length = i + j + 1 := by
      simp only [twoLoopWord, List.length_append, length_wordPower, List.length_singleton,
        Nat.mul_one]; omega
    have leftletter (i j m : Nat) (hm : m < i) : (twoLoopWord i j)[m]? = some 0 := by
      rw [twoLoopWord, List.getElem?_append_left (by
        simp only [List.length_append, length_wordPower, List.length_singleton, Nat.mul_one]
        omega),
        List.getElem?_append_left (by
          simp only [length_wordPower, List.length_singleton, Nat.mul_one]; exact hm),
        wordPower_getElem? _ _ _ (by simpa using hm)]
      rw [List.length_singleton, Nat.mod_one]
      rfl
    have separator (i j : Nat) : (twoLoopWord i j)[i]? = some 2 := by
      rw [twoLoopWord, List.getElem?_append_left (by
        simp only [List.length_append, length_wordPower, List.length_singleton, Nat.mul_one]
        omega),
        List.getElem?_append_right (by simp [length_wordPower]), length_wordPower]
      simp
    have winj (n : Nat) :
        Function.Injective (fun i : Fin (n + 1) => twoLoopWord i.val (n - i.val)) := by
      intro i j h
      apply Fin.ext
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have he := congrArg (fun U : List (Fin 3) => U[i.val]?) h
        rw [separator, leftletter _ _ _ hlt] at he
        exact (by decide : (2 : Fin 3) ≠ 0) (Option.some.inj he)
      · have he := congrArg (fun U : List (Fin 3) => U[j.val]?) h
        rw [leftletter _ _ _ hgt, separator] at he
        exact (by decide : (0 : Fin 3) ≠ 2) (Option.some.inj he)
    have fixedlen (n : Nat) (i : Fin (n + 1)) :
        (twoLoopWord i.val (n - i.val)).length = n + 1 := by
      rw [wlen]; have := i.isLt; omega
    have obstruction : ¬ ∃ T : Set (SinglePowerTemplate (Fin 3)), T.Finite ∧
        ∀ i j, ∃ t ∈ T, ∃ k : Nat, twoLoopWord i j = singlePowerOutput t k := by
      rintro ⟨T, hT, hcover⟩
      let : Fintype T := hT.fintype
      let N := Fintype.card T
      choose t ht k hk using (fun i : Fin (N + 1) => hcover i.val (N - i.val))
      let f : Fin (N + 1) → T := fun i => ⟨t i, ht i⟩
      have hf : Function.Injective f := by
        intro i j hij
        have htij : t i = t j := congrArg Subtype.val hij
        apply winj N
        change twoLoopWord i.val (N - i.val) = twoLoopWord j.val (N - j.val)
        rw [hk i, hk j, htij]
        by_cases hblock : (t j).block = []
        · simp [singlePowerOutput, hblock, wordPower]
        · have hi := fixedlen N i
          have hj := fixedlen N j
          rw [hk i, htij] at hi
          rw [hk j] at hj
          simp only [singlePowerOutput, List.length_append, length_wordPower] at hi hj
          have hmul : k i * (t j).block.length = k j * (t j).block.length := by omega
          have hpos : 0 < (t j).block.length := List.length_pos_iff_ne_nil.mpr hblock
          have hkeq : k i = k j := by nlinarith
          rw [hkeq]
      have hcard := Fintype.card_le_of_injective f hf
      simp only [Fintype.card_fin] at hcard
      change N + 1 ≤ N at hcard
      omega
    exact ⟨separated, leftcyclic, rightcyclic, coherent, crossing,
      fun n => ⟨winj n, fixedlen n⟩, obstruction⟩

end D5.S1.Words.ReturnWords.CoherentReturnPathTemplates
