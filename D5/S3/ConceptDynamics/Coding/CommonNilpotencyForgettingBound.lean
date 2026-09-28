/- GID: D5/S3/ConceptDynamics/Coding/CommonNilpotencyForgettingBound
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CommonNilpotencyForgettingBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fiber differences detect exact path forgetting with a finite dimension stopping bound. -/

import D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound

open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel

/-- Differences of actual states in a common fiber. -/
def differenceSpace {Q V : Type*} (p : Q → V) : Submodule ℚ (Q →₀ ℚ) :=
  Submodule.span ℚ {x | ∃ u v, p u = p v ∧ x = Finsupp.single u 1 - Finsupp.single v 1}

/-- The repeated sum of all generator images. -/
def imageChain {K M E : Type*} [Field K] [AddCommGroup M] [Module K M]
    (T : E → M →ₗ[K] M) (D : Submodule K M) : ℕ → Submodule K M
  | 0 => D
  | j + 1 => ⨆ a, (imageChain T D j).map (T a)

/-- Ordered products, with the first edge acting last on terminal states. -/
def wordOperator {K M E : Type*} [Field K] [AddCommGroup M] [Module K M]
    (T : E → M →ₗ[K] M) : List E → M →ₗ[K] M
  | [] => LinearMap.id
  | a :: w => (T a).comp (wordOperator T w)

/-- Linear extension on the terminal fiber, zero on the other fibers. -/
def edgeLinear {n : ℕ} {A : CountMat n n} {Q : Type}
    (L : IncomingLift A Q) (a : Edge A) : (Q →₀ ℚ) →ₗ[ℚ] Q →₀ ℚ :=
  Finsupp.linearCombination ℚ fun u =>
    if h : L.project u = a.target then Finsupp.single (L.lift a ⟨u, h⟩).val 1 else 0

/-- The numbered edge list of a compatible path. -/
def pathWord {n : ℕ} {A : CountMat n n} :
    {d : ℕ} → {i j : Fin n} → FinitePath A d i j → List (Edge A)
  | _, _, _, .nil _ => []
  | _, i, _, .cons (j := j) a tail => ⟨i, j, a⟩ :: pathWord tail

/-- Every actual path of this length is constant on its whole terminal fiber. -/
def Forgets {n : ℕ} {A : CountMat n n} {Q : Type}
    (L : IncomingLift A Q) (d : ℕ) : Prop :=
  ∀ (i j : Fin n) (p : FinitePath A d i j)
    (u v : {q : Q // L.project q = j}), L.liftPath p u = L.liftPath p v

private theorem difference_space_description {Q V : Type*} [Fintype Q] [Fintype V]
    (p : Q → V) (hp : Function.Surjective p) :
    differenceSpace p = LinearMap.ker (Finsupp.lmapDomain ℚ ℚ p) ∧
    Module.finrank ℚ (differenceSpace p) = Fintype.card Q - Fintype.card V := by
  classical
  let P := Finsupp.lmapDomain ℚ ℚ p
  let r : V → Q := Function.surjInv hp
  have hr : ∀ v, p (r v) = v := Function.rightInverse_surjInv hp
  have heq : differenceSpace p = LinearMap.ker P := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨u, v, huv, rfl⟩
      change P (_ - _) = 0
      rw [map_sub]
      simp [P, Finsupp.lmapDomain_apply, huv]
    · intro x hx
      have hzero : P x = 0 := hx
      let R := Finsupp.lmapDomain ℚ ℚ r
      have hdecomp : x - R (P x) =
          ∑ u : Q, x u • (Finsupp.single u 1 - Finsupp.single (r (p u)) 1) := by
        have hxexp : x = ∑ u : Q, x u • Finsupp.single u 1 := by
          ext u
          simp
        conv_lhs => rw [hxexp]
        simp only [map_sum, map_smul, P, R, Finsupp.lmapDomain_apply,
          Finsupp.mapDomain_single, Finset.sum_sub_distrib, smul_sub]
      rw [hzero, map_zero, sub_zero] at hdecomp
      rw [hdecomp]
      apply Submodule.sum_mem
      intro u _
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨u, r (p u), (hr _).symm, rfl⟩
  refine ⟨heq, ?_⟩
  have hsurj : Function.Surjective P := Finsupp.mapDomain_surjective hp
  have hdim := LinearMap.finrank_range_add_finrank_ker P
  rw [LinearMap.range_eq_top.mpr hsurj, _root_.finrank_top,
    Module.finrank_finsupp_self, Module.finrank_finsupp_self] at hdim
  rw [heq]
  omega

private theorem image_chain_analysis {K M E : Type*} [Field K] [AddCommGroup M]
    [Module K M] (T : E → M →ₗ[K] M) (D : Submodule K M) [FiniteDimensional K D]
    (hinv : ∀ a, D.map (T a) ≤ D) :
    (∀ j, imageChain T D j = ⨆ w : {w : List E // w.length = j},
      D.map (wordOperator T w.val)) ∧
    (∀ j, imageChain T D (j + 1) ≤ imageChain T D j) ∧
    (∀ j, imageChain T D (j + 1) = imageChain T D j →
      ∀ k, imageChain T D (j + k) = imageChain T D j) ∧
    (∀ d, imageChain T D d = ⊥ →
      ∃ m ≤ Module.finrank K D, imageChain T D m = ⊥ ∧
        ∀ k < m, imageChain T D k ≠ ⊥) := by
  classical
  have hmono : ∀ j, imageChain T D (j + 1) ≤ imageChain T D j := by
    intro j
    induction j with
    | zero => exact iSup_le hinv
    | succ j ih =>
      exact iSup_mono fun a => Submodule.map_mono ih
  have hanti : Antitone (imageChain T D) := antitone_nat_of_succ_le hmono
  have hle : ∀ j, imageChain T D j ≤ D := fun j => hanti (Nat.zero_le j)
  have hstable : ∀ j, imageChain T D (j + 1) = imageChain T D j →
      ∀ k, imageChain T D (j + k) = imageChain T D j := by
    intro j hj k
    induction k with
    | zero => rfl
    | succ k ih =>
      change (⨆ a, (imageChain T D (j + k)).map (T a)) = _
      rw [ih]
      exact hj
  refine ⟨?_, hmono, hstable, ?_⟩
  · intro j
    induction j with
    | zero =>
      apply le_antisymm
      · exact le_iSup_of_le ⟨[], rfl⟩ (by simp [imageChain, wordOperator])
      · apply iSup_le
        rintro ⟨w, hw⟩
        have : w = [] := List.length_eq_zero_iff.mp hw
        subst w
        simp [imageChain, wordOperator]
    | succ j ih =>
      change (⨆ a, (imageChain T D j).map (T a)) = _
      rw [ih]
      simp only [Submodule.map_iSup]
      apply le_antisymm
      · refine iSup_le fun a => iSup_le fun w => ?_
        apply le_iSup_of_le ⟨a :: w.val, by simp [w.property]⟩
        simp [wordOperator, Submodule.map_comp]
      · refine iSup_le fun w => ?_
        rcases w with ⟨w, hw⟩
        cases w with
        | nil => simp at hw
        | cons a w =>
          have hw' : w.length = j := by simpa using hw
          apply le_iSup_of_le a
          apply le_iSup_of_le ⟨w, hw'⟩
          simp [wordOperator, Submodule.map_comp]
  · intro d hd
    have hex : ∃ j, imageChain T D j = ⊥ := ⟨d, hd⟩
    let m := Nat.find hex
    have hm : imageChain T D m = ⊥ := Nat.find_spec hex
    have hmin : ∀ k < m, imageChain T D k ≠ ⊥ := fun k hk => Nat.find_min hex hk
    have hdrop : ∀ k < m, imageChain T D (k + 1) < imageChain T D k := by
      intro k hk
      refine lt_of_le_of_ne (hmono k) ?_
      intro heq
      have hs := hstable k heq (m - k)
      rw [Nat.add_sub_of_le hk.le, hm] at hs
      exact hmin k hk hs.symm
    have hdim : ∀ k ≤ m, Module.finrank K (imageChain T D k) + k ≤ Module.finrank K D := by
      intro k hk
      induction k with
      | zero => exact le_rfl
      | succ k ih =>
        have hk' : k < m := by omega
        have := ih (by omega)
        let : FiniteDimensional K (imageChain T D k) :=
          Submodule.finiteDimensional_of_le (hle k)
        have hlt := Submodule.finrank_lt_finrank_of_lt (hdrop k hk')
        omega
    exact ⟨m, by have := hdim m le_rfl; omega, hm, hmin⟩

/-- Ordered products on a fixed terminal fiber either vanish or follow one
compatible path with exactly that numbered edge word. -/
private theorem word_fiber_action {n : ℕ} {A : CountMat n n} {Q : Type}
    (L : IncomingLift A Q) (w : List (Edge A)) (j : Fin n) :
    (∀ u : {q : Q // L.project q = j},
      wordOperator (edgeLinear L) w (Finsupp.single u.val 1) = 0) ∨
    (∃ (i : Fin n) (p : FinitePath A w.length i j), pathWord p = w ∧
      ∀ u : {q : Q // L.project q = j},
        wordOperator (edgeLinear L) w (Finsupp.single u.val 1) =
          Finsupp.single (L.liftPath p u).val 1) := by
  classical
  induction w with
  | nil => exact Or.inr ⟨j, .nil j, rfl, fun _ => rfl⟩
  | cons a w ih =>
    rcases ih with hzero | ⟨i, p, hp, hact⟩
    · left
      intro u
      simp [wordOperator, hzero u]
    · rcases a with ⟨s, t, a⟩
      by_cases ht : t = i
      · subst t
        right
        refine ⟨s, .cons a p, ?_, ?_⟩
        · simp [pathWord, hp]
        · intro u
          change edgeLinear L ⟨s, i, a⟩
            (wordOperator (edgeLinear L) w (Finsupp.single u.val 1)) = _
          rw [hact u]
          simp [edgeLinear, (L.liftPath p u).property, IncomingLift.liftPath]
      · left
        intro u
        change edgeLinear L ⟨s, t, a⟩
          (wordOperator (edgeLinear L) w (Finsupp.single u.val 1)) = _
        rw [hact u]
        simp [edgeLinear, (L.liftPath p u).property, Ne.symm ht]

/-- Linearization is faithful to actual state equality, including empty paths. -/
private theorem forgetting_linearization {n : ℕ} {A : CountMat n n} {Q : Type}
    (L : IncomingLift A Q) :
    (∀ a, (differenceSpace L.project).map (edgeLinear L a) ≤ differenceSpace L.project) ∧
    (∀ d, Forgets L d ↔ ∀ w : List (Edge A), w.length = d →
      (differenceSpace L.project).map (wordOperator (edgeLinear L) w) = ⊥) ∧
    (∀ (w : List (Edge A)),
      (∀ (i j : Fin n) (p : FinitePath A w.length i j), pathWord p ≠ w) →
      wordOperator (edgeLinear L) w = 0) ∧
    (∀ {d : ℕ} {i j : Fin n} (p : FinitePath A d i j),
      (pathWord p).length = d ∧
      ∀ u : {q : Q // L.project q = j},
        wordOperator (edgeLinear L) (pathWord p) (Finsupp.single u.val 1) =
          Finsupp.single (L.liftPath p u).val 1) := by
  classical
  have hsingle (a : Edge A) (u : Q) :
      edgeLinear L a (Finsupp.single u 1) =
        if h : L.project u = a.target then Finsupp.single (L.lift a ⟨u, h⟩).val 1 else 0 := by
    simp [edgeLinear]
  have hgen (u v : Q) (h : L.project u = L.project v) :
      Finsupp.single u (1 : ℚ) - Finsupp.single v 1 ∈ differenceSpace L.project :=
    Submodule.subset_span ⟨u, v, h, rfl⟩
  have hpath : ∀ {d : ℕ} {i j : Fin n} (p : FinitePath A d i j),
      (pathWord p).length = d ∧
      ∀ u : {q : Q // L.project q = j},
        wordOperator (edgeLinear L) (pathWord p) (Finsupp.single u.val 1) =
          Finsupp.single (L.liftPath p u).val 1 := by
    intro d i j p
    induction p with
    | nil i => exact ⟨rfl, fun _ => rfl⟩
    | @cons d i j k a p ih =>
      refine ⟨by simp [pathWord, ih.1], ?_⟩
      intro u
      change edgeLinear L ⟨i, j, a⟩
        (wordOperator (edgeLinear L) (pathWord p) (Finsupp.single u.val 1)) = _
      rw [ih.2 u, hsingle]
      simp [IncomingLift.liftPath, (L.liftPath p u).property]
  refine ⟨?_, ?_, ?_, hpath⟩
  · intro a
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro x ⟨u, v, huv, rfl⟩
    change edgeLinear L a (_ - _) ∈ differenceSpace L.project
    rw [map_sub, hsingle, hsingle]
    by_cases hu : L.project u = a.target
    · have hv := huv.symm.trans hu
      simp only [dif_pos hu, dif_pos hv]
      exact hgen _ _ ((L.lift a ⟨u, hu⟩).property.trans (L.lift a ⟨v, hv⟩).property.symm)
    · have hv : L.project v ≠ a.target := fun h => hu (huv.trans h)
      simp only [dif_neg hu, dif_neg hv, sub_self]
      exact Submodule.zero_mem _
  · intro d
    constructor
    · intro hf w hw
      apply le_antisymm ?_ bot_le
      rw [Submodule.map_le_iff_le_comap]
      apply Submodule.span_le.mpr
      rintro x ⟨u, v, huv, rfl⟩
      change wordOperator (edgeLinear L) w (_ - _) = 0
      rw [map_sub]
      rcases word_fiber_action L w (L.project u) with hz | ⟨i, p, _, hp⟩
      · rw [hz ⟨u, rfl⟩, hz ⟨v, huv.symm⟩, sub_self]
      · have hconst : L.liftPath p ⟨u, rfl⟩ = L.liftPath p ⟨v, huv.symm⟩ := by
          subst d
          exact hf i _ p _ _
        rw [hp ⟨u, rfl⟩, hp ⟨v, huv.symm⟩, hconst, sub_self]
    · intro hz i j p u v
      have hx := hgen u.val v.val (u.property.trans v.property.symm)
      have himage : wordOperator (edgeLinear L) (pathWord p)
          (Finsupp.single u.val 1 - Finsupp.single v.val 1) ∈
          (differenceSpace L.project).map (wordOperator (edgeLinear L) (pathWord p)) :=
        ⟨_, hx, rfl⟩
      rw [hz _ (hpath p).1] at himage
      have heq : wordOperator (edgeLinear L) (pathWord p)
          (Finsupp.single u.val 1 - Finsupp.single v.val 1) = 0 := himage
      rw [map_sub, (hpath p).2 u, (hpath p).2 v, sub_eq_zero] at heq
      exact Subtype.ext (Finsupp.single_left_injective (by norm_num : (1 : ℚ) ≠ 0) heq)
  · intro w hn
    apply Finsupp.lhom_ext
    intro u c
    have hz : wordOperator (edgeLinear L) w (Finsupp.single u 1) = 0 := by
      rcases word_fiber_action L w (L.project u) with h | ⟨i, p, hp, _⟩
      · exact h ⟨u, rfl⟩
      · exact (hn i _ p hp).elim
    have hs : Finsupp.single u c = c • Finsupp.single u (1 : ℚ) := by simp
    rw [hs, map_smul, hz, smul_zero]
    rfl

/-- Exact forgetting, common annihilation, and the descending image algorithm.
The space is represented inside the free vector space on the actual states;
its kernel description imposes zero coefficient sum separately in every fiber. -/
theorem common_nilpotency_forgetting_bound {n : ℕ} {A : CountMat n n} {Q : Type}
    [Fintype Q] (L : IncomingLift A Q) :
    let D := differenceSpace L.project
    let T := edgeLinear L
    let W := imageChain T D
    D = LinearMap.ker (Finsupp.lmapDomain ℚ ℚ L.project) ∧
    Module.finrank ℚ D = Fintype.card Q - n ∧
    (∀ a, D.map (T a) ≤ D) ∧
    (∀ (w : List (Edge A)),
      (∀ (i j : Fin n) (p : FinitePath A w.length i j), pathWord p ≠ w) →
      wordOperator T w = 0) ∧
    (∀ d, Forgets L d ↔ ∀ w : List (Edge A), w.length = d →
      D.map (wordOperator T w) = ⊥) ∧
    (∀ w : List (Edge A), D.map (wordOperator T w) = ⊥ ↔
      (wordOperator T w).domRestrict D = 0) ∧
    (∀ {d : ℕ} {i j : Fin n} (p : FinitePath A d i j),
      (pathWord p).length = d ∧
      ∀ u : {q : Q // L.project q = j},
        wordOperator T (pathWord p) (Finsupp.single u.val 1) =
          Finsupp.single (L.liftPath p u).val 1) ∧
    W 0 = D ∧
    (∀ j, W (j + 1) = ⨆ a, (W j).map (T a)) ∧
    (∀ j, W j = ⨆ w : {w : List (Edge A) // w.length = j},
      D.map (wordOperator T w.val)) ∧
    (∀ j, W (j + 1) ≤ W j) ∧
    (∀ j, W (j + 1) = W j → ∀ k, W (j + k) = W j) ∧
    (∀ d, Forgets L d ↔ W d = ⊥) ∧
    (∀ d, IsLeast {j | Forgets L j} d ↔ IsLeast {j | W j = ⊥} d) ∧
    ((∃ d, Forgets L d) → ∃ d ≤ Fintype.card Q - n, IsLeast {j | Forgets L j} d) ∧
    ((∃ d, Forgets L d) ↔ W (Fintype.card Q - n) = ⊥) := by
  classical
  dsimp only
  let D := differenceSpace L.project
  let T := edgeLinear L
  let W := imageChain T D
  obtain ⟨hker, hdim⟩ := difference_space_description L.project L.onto
  simp only [Fintype.card_fin] at hdim
  obtain ⟨hinv, hlin, hincompat, hpath⟩ := forgetting_linearization L
  obtain ⟨himages, hmono, hstable, hbound⟩ := image_chain_analysis T D hinv
  have hiff (d : ℕ) : Forgets L d ↔ W d = ⊥ := by
    change Forgets L d ↔ imageChain T D d = ⊥
    rw [hlin, himages, iSup_eq_bot]
    constructor
    · intro h w
      exact h w.val w.property
    · intro h w hw
      exact h ⟨w, hw⟩
  have hleast : (∃ d, Forgets L d) →
      ∃ d ≤ Fintype.card Q - n, IsLeast {j | Forgets L j} d := by
    rintro ⟨d, hd⟩
    obtain ⟨m, hm, hz, hmin⟩ := hbound d ((hiff d).mp hd)
    refine ⟨m, hdim ▸ hm, (hiff m).mpr hz, ?_⟩
    intro k hk
    by_contra h
    exact hmin k (by omega) ((hiff k).mp hk)
  have hzero (w : List (Edge A)) : D.map (wordOperator T w) = ⊥ ↔
      (wordOperator T w).domRestrict D = 0 := by
    rw [← LinearMap.range_domRestrict, LinearMap.range_eq_bot]
  refine ⟨hker, hdim, hinv, hincompat, hlin, hzero, hpath, rfl, fun _ => rfl,
    himages, hmono, hstable, hiff, ?_, hleast, ?_⟩
  · intro d
    have heq : {j | Forgets L j} = {j | W j = ⊥} := Set.ext hiff
    rw [heq]
  · constructor
    · intro h
      obtain ⟨d, hd, hmin⟩ := hleast h
      have hanti : Antitone W := antitone_nat_of_succ_le hmono
      apply le_antisymm ?_ bot_le
      calc
        W (Fintype.card Q - n) ≤ W d := hanti hd
        _ = ⊥ := (hiff d).mp hmin.1
    · intro h
      exact ⟨Fintype.card Q - n, (hiff _).mpr h⟩

#print axioms common_nilpotency_forgetting_bound

end D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound
