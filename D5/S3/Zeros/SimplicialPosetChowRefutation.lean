/- GID: D5/S3/Zeros/SimplicialPosetChowRefutation
   generality: I
   mirror-B: D5/B/S3/Zeros/SimplicialPosetChowRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Zeros/SimplicialPosetChowRefutation.claim; result=D5/S3/Zeros/SimplicialPosetChowRefutation.result; claim=D5/S3/Zeros/SimplicialPosetChowRefutation.claim
   digest: Two tetrahedra sharing a vertex refute simplicial-poset Chow real-rootedness. -/
/- result
   proof_shape: content
   escape_witness: H_P2 (intrinsic-rank flag evaluation), using finset_height.
   admission_basis: open-problem-resolution (#14658; Refuted)
   Direct frozen dependency: D5/S3/Zeros/Jensen/JensenPolynomialObstruction.PolynomialHyperbolic
   declaration statement_id: sha256:cd221a568336243c01b18910265c1433fcdbd1ac60fbaceaecf37400efce9ac8.
   Information-escape registration is paused under CLAUDE.md §3.9.
   finset_height: proof_shape: content; consumers: face_height.
   face_height: proof_shape: content; consumers: rank_eq_card.
   alphaUsing_all_subsets: proof_shape: bind-only; consumers: alphaUsing_chainSubsets.
   maxChain_iff: proof_shape: bind-only; consumers: alpha_card.
   chainSubsets_eq: proof_shape: content; consumers: chainSubsetsFinset, chainSubsetsFinset_eq.
   chainSubsetsFinset_eq: proof_shape: content; consumers: alpha_card, alphaUsing_chainSubsets.
   alpha_card: proof_shape: content; consumers: alpha_P2_using.
   alphaUsing_chainSubsets: proof_shape: content; consumers: alpha_P2_using.
   alphaSelected_empty: proof_shape: bind-only; consumers: alphaSelected_all.
   alphaSelected_two: proof_shape: bind-only; consumers: alphaSelected_all.
   alphaSelected_three: proof_shape: bind-only; consumers: alphaSelected_all.
   alphaSelected_four: proof_shape: bind-only; consumers: alphaSelected_all.
   alphaSelected_two_four: proof_shape: bind-only; consumers: alphaSelected_all.
   alphaSelected_all: proof_shape: bind-only; consumers: alpha_P2_using.
   alpha_P2_using: proof_shape: content; consumers: H_card.
   K2_down: proof_shape: bind-only; consumers: interval_four, rank_eq_card.
   maximal_iff: proof_shape: bind-only; consumers: interval_four.
   P2_simplicial: proof_shape: content; consumers: result.
   rank_eq_card: proof_shape: content; consumers: alpha_card.
   alpha0_card: proof_shape: bind-only; consumers: beta0_card, beta2_card, beta3_card, beta4_card, beta24_card.
   alpha2_card: proof_shape: bind-only; consumers: beta2_card, beta24_card.
   alpha3_card: proof_shape: bind-only; consumers: beta3_card.
   alpha4_card: proof_shape: bind-only; consumers: beta4_card, beta24_card.
   alpha24_card: proof_shape: bind-only; consumers: beta24_card.
   beta0_card: proof_shape: bind-only; consumers: H_P2.
   beta2_card: proof_shape: bind-only; consumers: H_P2.
   beta3_card: proof_shape: bind-only; consumers: H_P2.
   beta4_card: proof_shape: bind-only; consumers: H_P2.
   beta24_card: proof_shape: bind-only; consumers: H_P2.
   isolated_four: proof_shape: bind-only; consumers: alphaSelected_all, H_P2.
   H_card: proof_shape: content; consumers: H_P2.
   H_P2: proof_shape: content; consumers: H_P2_factorization.
   a_bounds: proof_shape: bind-only; consumers: z_quadratic, z_im_ne.
   a_add_b: proof_shape: bind-only; consumers: quartic_factorization.
   a_mul_b: proof_shape: bind-only; consumers: quartic_factorization.
   quartic_factorization: proof_shape: bind-only; consumers: H_P2_factorization.
   z_quadratic: proof_shape: bind-only; consumers: H_P2_root.
   z_im_ne: proof_shape: bind-only; consumers: result.
   H_P2_factorization: proof_shape: content; consumers: H_P2_root.
   H_P2_root: proof_shape: content; consumers: result.
-/
import D5.S3.Zeros.Jensen.JensenPolynomialObstruction
import Mathlib.Data.Fintype.WithTopBot
import Mathlib.Order.KrullDimension
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.QuadraticDiscriminant
set_option autoImplicit false
set_option Elab.async false
namespace D5.S3.Zeros.SimplicialPosetChowRefutation
open Finset Polynomial
/-- Finset cardinality is the order height in the inclusion order. -/
private theorem finset_height {V : Type} (s : Finset V) :
    Order.height s = (s.card : ℕ∞) := by
  classical
  have upper (t : Finset V) : Order.height t ≤ (t.card : ℕ∞) := by
    simpa only [Order.height_nat] using
      Order.height_le_height_apply_of_strictMono Finset.card Finset.card_strictMono t
  apply le_antisymm (upper s)
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : s < insert a s := Finset.ssubset_insert ha
    have h := Order.height_add_one_le hs
    exact le_trans (by simpa only [Finset.card_insert_of_notMem ha, Nat.cast_add,
      Nat.cast_one, add_comm] using add_le_add_right ih 1) h
/-- Height is preserved when the carrier is a lower closed collection of finite sets. -/
private theorem face_height {V : Type} (K : Set (Finset V))
    (down : ∀ ⦃s t⦄, s ⊆ t → t ∈ K → s ∈ K) (x : K) :
    Order.height x = (x.val.card : ℕ∞) := by
  classical
  rw [Order.height_eq_of_strictMono (fun y : K => y.val)
    (fun _ _ h => h) ?_ x, finset_height]
  intro a b hb
  exact ⟨⟨b, down (le_of_lt hb) a.property⟩, hb, rfl⟩
/-- The lower interval at any face is the Boolean lattice on its vertices. -/
private def face_interval_iso {V : Type} [DecidableEq V] (K : Set (Finset V))
    (down : ∀ ⦃s t⦄, s ⊆ t → t ∈ K → s ∈ K) (x : K) :
    Set.Iic x ≃o Finset x.val where
  toFun y := y.val.val.subtype (· ∈ x.val)
  invFun s := ⟨⟨s.map (Function.Embedding.subtype _),
    down (by
      intro a ha
      exact Finset.property_of_mem_map_subtype s ha) x.property⟩,
    by
      intro a ha
      exact Finset.property_of_mem_map_subtype s ha⟩
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    exact Finset.subtype_map_of_mem y.property
  right_inv s := by
    ext a
    simp only [Finset.mem_subtype, Finset.mem_map]
    constructor
    · rintro ⟨b, hb, he⟩
      exact (Subtype.ext he : b = a) ▸ hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  map_rel_iff' := by
    intro a b
    constructor
    · intro h v hv
      have hvx : v ∈ x.val := a.property hv
      exact Finset.mem_subtype.mp (h (Finset.mem_subtype.mpr hv :
        (⟨v, hvx⟩ : x.val) ∈ a.val.val.subtype (· ∈ x.val)))
    · intro h v hv
      exact Finset.mem_subtype.mpr (h (Finset.mem_subtype.mp hv))
noncomputable def rank {P : Type} [PartialOrder P] (x : P) : ℕ :=
  (Order.height x).toNat
def simplicial (P : Type) [Fintype P] [DecidableEq P] [PartialOrder P] [OrderBot P]
    (n : ℕ) : Prop :=
  ∀ m : P, IsMax m → Nonempty (Set.Iic m ≃o Finset (Fin n))
private instance chainDecidable (P : Type) [DecidableEq P] [PartialOrder P]
    [DecidableLE P] (C : Finset P) : Decidable (IsChain (· ≤ ·) (C : Set P)) :=
  inferInstanceAs (Decidable (∀ x ∈ C, ∀ y ∈ C, x ≠ y → x ≤ y ∨ y ≤ x))
private def alphaUsing (P : Type) [Fintype P] [DecidableEq P] [PartialOrder P]
    [DecidableLE P] (r : P → ℕ) (T : Finset ℕ) : ℕ :=
  letI : DecidablePred (fun C : Finset P => IsChain (· ≤ ·) (C : Set P)) :=
    fun C => chainDecidable P C
  ((Finset.univ.powersetCard T.card).filter
    (fun C : Finset P => IsChain (· ≤ ·) (C : Set P) ∧ C.image r = T)).card
open scoped Classical in
private theorem alphaUsing_all_subsets (P : Type) [Fintype P] [DecidableEq P]
    [PartialOrder P] [DecidableLE P] (r : P → ℕ) (T : Finset ℕ) :
    alphaUsing P r T =
      ((Finset.univ : Finset P).powerset.filter (fun C : Finset P =>
        IsChain (· ≤ ·) (C : Set P) ∧ C.image r = T ∧ C.card = T.card)).card := by
  unfold alphaUsing
  congr 1
  ext C
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_powerset,
    Finset.subset_univ, true_and]
  tauto
noncomputable def alpha (P : Type) [Fintype P] [DecidableEq P] [PartialOrder P]
    [OrderBot P] (n : ℕ) (T : Finset ℕ) : ℕ := by
  classical
  let Q := {x : WithTop P // x = ⊥ ∨ x = ⊤ ∨ WithTop.recTopCoe (n + 1) rank x ∈ T}
  exact ((Finset.univ : Finset Q).powerset.filter
    (fun C : Finset Q => IsMaxChain (· ≤ ·) (C : Set Q))).card
private def betaUsing (P : Type) [Fintype P] [DecidableEq P] [PartialOrder P]
    [DecidableLE P] (r : P → ℕ) (S : Finset ℕ) : ℤ :=
  ∑ T ∈ S.powerset, (-1 : ℤ) ^ (S \ T).card * (alphaUsing P r T : ℤ)
noncomputable def beta (P : Type) [Fintype P] [DecidableEq P] [PartialOrder P]
    [OrderBot P] (n : ℕ) (S : Finset ℕ) : ℤ := by
  classical
  exact ∑ T ∈ S.powerset, (-1 : ℤ) ^ (S \ T).card * (alpha P n T : ℤ)
def isolated (S : Finset ℕ) : Prop := ∀ i ∈ S, i + 1 ∉ S
private instance isolatedDecidable (S : Finset ℕ) : Decidable (isolated S) :=
  inferInstanceAs (Decidable (∀ i ∈ S, i + 1 ∉ S))
private noncomputable def HUsing (P : Type) [Fintype P] [DecidableEq P] [PartialOrder P]
    [DecidableLE P] (r : P → ℕ) (n : ℕ) : Polynomial ℤ :=
  ∑ S ∈ (Finset.Icc 2 n).powerset.filter isolated,
    C (betaUsing P r S) * X ^ S.card * (1 + X) ^ (n - 2 * S.card)
noncomputable def H (P : Type) [Fintype P] [DecidableEq P] [PartialOrder P]
    [OrderBot P] (n : ℕ) : Polynomial ℤ := by
  classical
  exact ∑ S ∈ (Finset.Icc 2 n).powerset.filter isolated,
    C (beta P n S) * X ^ S.card * (1 + X) ^ (n - 2 * S.card)
noncomputable def claim : Prop :=
  ∀ (P : Type) [Fintype P] [DecidableEq P] [PartialOrder P] [OrderBot P] (n : ℕ),
    simplicial P n →
      D5.S3.Zeros.Jensen.JensenPolynomialObstruction.PolynomialHyperbolic
        ((H P n).map (Int.castRingHom ℝ))
open Finset Polynomial
private def facetA : Finset (Fin 7) := {0, 1, 2, 3}
private def facetB : Finset (Fin 7) := {0, 4, 5, 6}
private def K2 (s : Finset (Fin 7)) : Prop := s ⊆ facetA ∨ s ⊆ facetB
private instance kTwoDecidable : DecidablePred K2 := fun s => inferInstanceAs
  (Decidable (s ⊆ facetA ∨ s ⊆ facetB))
private instance faceOrderBot : OrderBot {s : Finset (Fin 7) // K2 s} :=
  Subtype.orderBot (Or.inl (Finset.empty_subset _))
private def fa : {s : Finset (Fin 7) // K2 s} := ⟨facetA, Or.inl (subset_refl _)⟩
private def fb : {s : Finset (Fin 7) // K2 s} := ⟨facetB, Or.inr (subset_refl _)⟩
private theorem K2_down {s t : Finset (Fin 7)} (h : s ⊆ t) (ht : K2 t) : K2 s :=
  ht.elim (fun ha => Or.inl (h.trans ha)) (fun hb => Or.inr (h.trans hb))
private theorem maximal_iff (x : {s : Finset (Fin 7) // K2 s}) : IsMax x ↔ x = fa ∨ x = fb := by
  constructor
  · intro hm
    rcases x.property with ha | hb
    · exact Or.inl (le_antisymm ha (hm ha))
    · exact Or.inr (le_antisymm hb (hm hb))
  · rintro (rfl | rfl) y hy
    · rcases y.property with ha | hb
      · exact ha
      · exact False.elim ((by decide : ¬ facetA ⊆ facetB) ((show facetA ⊆ y.val from hy).trans hb))
    · rcases y.property with ha | hb
      · exact False.elim ((by decide : ¬ facetB ⊆ facetA) ((show facetB ⊆ y.val from hy).trans ha))
      · exact hb
private def finset_congr_iso {A B : Type} (e : A ≃ B) : Finset A ≃o Finset B where
  toEquiv := e.finsetCongr
  map_rel_iff' := Finset.map_subset_map
private noncomputable def interval_four (x : {s : Finset (Fin 7) // K2 s}) (hx : IsMax x) :
    Set.Iic x ≃o Finset (Fin 4) := by
  have hc : x.val.card = 4 := by
    rcases (maximal_iff x).mp hx with rfl | rfl <;> decide
  exact (face_interval_iso {s | K2 s} (by intro s t h ht; exact K2_down h ht) x).trans
    (finset_congr_iso (Finset.orderIsoOfFin x.val hc).toEquiv.symm)
private theorem P2_simplicial : simplicial {s : Finset (Fin 7) // K2 s} 4 := fun x hx => ⟨interval_four x hx⟩
private theorem rank_eq_card (x : {s : Finset (Fin 7) // K2 s}) : rank x = x.val.card := by
  unfold rank
  rw [face_height {s | K2 s} (by intro s t h ht; exact K2_down h ht) x]
  simp
set_option maxRecDepth 4096 in
private theorem alpha0_card :
    alphaUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) ∅ = 1 := by decide +kernel
set_option maxRecDepth 4096 in
private theorem alpha2_card :
    alphaUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) {2} = 12 := by decide +kernel
set_option maxRecDepth 4096 in
private theorem alpha3_card :
    alphaUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) {3} = 8 := by decide +kernel
set_option maxRecDepth 4096 in
private theorem alpha4_card :
    alphaUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) {4} = 2 := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- Enumerating all two-face chains requires the finite comparison table.
private theorem alpha24_card :
    alphaUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) {2,4} = 12 := by decide +kernel
private theorem beta0_card :
    betaUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) ∅ = 1 := by
  norm_num [betaUsing, alpha0_card]
private theorem beta2_card :
    betaUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) {2} = 11 := by
  have hp : ({2} : Finset ℕ).powerset = {∅,{2}} := by decide
  rw [betaUsing, hp]
  norm_num [Finset.sum_insert, Finset.sum_singleton, alpha0_card, alpha2_card]
private theorem beta3_card :
    betaUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) {3} = 7 := by
  have hp : ({3} : Finset ℕ).powerset = {∅,{3}} := by decide
  rw [betaUsing, hp]
  norm_num [Finset.sum_insert, Finset.sum_singleton, alpha0_card, alpha3_card]
private theorem beta4_card :
    betaUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) {4} = 1 := by
  have hp : ({4} : Finset ℕ).powerset = {∅,{4}} := by decide
  rw [betaUsing, hp]
  norm_num [Finset.sum_insert, Finset.sum_singleton, alpha0_card, alpha4_card]
private theorem beta24_card :
    betaUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) {2,4} = -1 := by
  have hp : ({2,4} : Finset ℕ).powerset = {∅,{2},{4},{2,4}} := by decide
  rw [betaUsing, hp, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have hd : ({2,4} : Finset ℕ) \ {2} = {4} := by decide
  rw [hd]
  norm_num [alpha0_card, alpha2_card, alpha4_card, alpha24_card]
private theorem isolated_four : ((Finset.Icc 2 4).powerset.filter isolated) =
    {∅,{2},{3},{4},{2,4}} := by decide
private theorem maxChain_iff {P : Type} [PartialOrder P] (C : Set P) :
    IsMaxChain (· ≤ ·) C ↔ IsChain (· ≤ ·) C ∧
      ∀ x : P, (∀ y ∈ C, x ≤ y ∨ y ≤ x) → x ∈ C := by
  constructor
  · intro hc
    refine ⟨hc.isChain, fun x hx => ?_⟩
    exact (Flag.mem_iff_forall_le_or_ge (s := Flag.ofIsMaxChain C hc)).mpr
      (fun {_} hy => hx _ hy)
  · rintro ⟨hc, hm⟩
    refine ⟨hc, fun D hd hcd => Set.Subset.antisymm hcd ?_⟩
    intro x hx
    exact hm x (fun y hy => hd.total hx (hcd hy))
private def chainSubsets {P : Type} [PartialOrder P] [DecidableEq P] [DecidableLE P] :
    List P → Finset (Finset P)
  | [] => {∅}
  | x :: xs =>
    let cs := chainSubsets xs
    cs ∪ (cs.filter (fun C => ∀ y ∈ C, x ≤ y ∨ y ≤ x)).image (insert x)
private theorem chainSubsets_eq {P : Type} [PartialOrder P] [DecidableEq P]
    [DecidableLE P] (xs : List P)
    [DecidablePred (fun C : Finset P => IsChain (· ≤ ·) (C : Set P))] :
    chainSubsets xs = xs.toFinset.powerset.filter (fun C : Finset P =>
      IsChain (· ≤ ·) (C : Set P)) := by
  induction xs with
  | nil =>
    ext C
    simp only [chainSubsets, List.toFinset_nil, Finset.powerset_empty,
      Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, by simpa only [Finset.coe_empty] using
        (IsChain.empty : IsChain (· ≤ ·) (∅ : Set P))⟩
    · exact And.left
  | cons x xs ih =>
    rw [chainSubsets, ih]
    ext C
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_powerset, List.toFinset_cons]
    constructor
    · rintro (⟨hs, hc⟩ | ⟨D, ⟨⟨hs, hc⟩, hcomp⟩, rfl⟩)
      · exact ⟨hs.trans (subset_insert _ _), hc⟩
      · exact ⟨insert_subset_insert x hs, by
          simpa only [Finset.coe_insert] using hc.insert (fun y hy _ => hcomp y hy)⟩
    · rintro ⟨hs, hc⟩
      by_cases hx : x ∈ C
      · right
        refine ⟨C.erase x, ⟨⟨?_, hc.mono (by simp)⟩, ?_⟩, insert_erase hx⟩
        · intro y hy
          have h := hs (mem_of_mem_erase hy)
          rcases mem_insert.mp h with rfl | h
          · exact False.elim ((mem_erase.mp hy).1 rfl)
          · exact h
        · intro y hy
          exact hc.total hx (mem_of_mem_erase hy)
      · left
        refine ⟨?_, hc⟩
        intro y hy
        exact (mem_insert.mp (hs hy)).resolve_left (fun h => hx (h ▸ hy))
private def chainSubsetsFinset {P : Type} [PartialOrder P] [DecidableEq P] [DecidableLE P]
    (s : Finset P) : Finset (Finset P) :=
  Quot.liftOn s.val chainSubsets (by
    intro xs ys h
    let : DecidablePred (fun C : Finset P => IsChain (· ≤ ·) (C : Set P)) :=
      fun C => chainDecidable P C
    rw [chainSubsets_eq, chainSubsets_eq, List.toFinset_eq_of_perm xs ys h])
private theorem chainSubsetsFinset_eq {P : Type} [PartialOrder P] [DecidableEq P]
    [DecidableLE P] (s : Finset P)
    [DecidablePred (fun C : Finset P => IsChain (· ≤ ·) (C : Set P))] :
    chainSubsetsFinset s = s.powerset.filter (fun C : Finset P => IsChain (· ≤ ·) (C : Set P)) := by
  rcases s with ⟨s, hs⟩
  revert hs
  refine Quotient.inductionOn s ?_
  intro xs hs
  have he : (⟨(xs : Multiset P), hs⟩ : Finset P) = xs.toFinset := by
    ext x
    change x ∈ (xs : Multiset P) ↔ x ∈ xs.toFinset
    simp only [Multiset.mem_coe, List.mem_toFinset]
  change chainSubsets xs = ((⟨(xs : Multiset P), hs⟩ : Finset P).powerset.filter
    (fun C : Finset P => IsChain (· ≤ ·) (C : Set P)))
  rw [he]
  exact chainSubsets_eq xs
private def alphaSelectedUsing (P : Type) [Fintype P] [DecidableEq P]
    [PartialOrder P] [DecidableLE P] [OrderBot P] (r : P → ℕ) (n : ℕ) (T : Finset ℕ) : ℕ :=
  let Q := {x : WithTop P // x = ⊥ ∨ x = ⊤ ∨ WithTop.recTopCoe (n+1) r x ∈ T}
  ((chainSubsetsFinset (Finset.univ : Finset Q)).filter
    (fun C => ∀ x : Q, (∀ y ∈ C, x ≤ y ∨ y ≤ x) → x ∈ C)).card
private theorem alpha_card (T : Finset ℕ) :
    alpha {s : Finset (Fin 7) // K2 s} 4 T =
    alphaSelectedUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) 4 T := by
  classical
  have hr : (rank : {s : Finset (Fin 7) // K2 s} → ℕ) = (fun x => x.val.card) :=
    funext rank_eq_card
  unfold alpha
  rw [hr]
  unfold alphaSelectedUsing
  dsimp only
  rw [chainSubsetsFinset_eq]
  simp only [Finset.filter_filter]
  apply congrArg Finset.card
  ext C
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
  rw [maxChain_iff]
  tauto
private theorem alphaUsing_chainSubsets (P : Type) [Fintype P] [DecidableEq P]
    [PartialOrder P] [DecidableLE P] (r : P → ℕ) (T : Finset ℕ) :
    alphaUsing P r T = ((chainSubsetsFinset ((Finset.univ : Finset P).filter (fun x => r x ∈ T))).filter
      (fun C => C.image r = T ∧ C.card = T.card)).card := by
  let : DecidablePred (fun C : Finset P => IsChain (· ≤ ·) (C : Set P)) :=
    fun C => chainDecidable P C
  rw [alphaUsing_all_subsets, chainSubsetsFinset_eq, Finset.filter_filter]
  apply congrArg Finset.card
  ext C
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
  constructor
  · rintro ⟨hc, hi, hn⟩
    refine ⟨?_, hc, hi, hn⟩
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hi ▸ Finset.mem_image_of_mem r hx⟩
  · rintro ⟨_, hc, hi, hn⟩
    exact ⟨hc, hi, hn⟩
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem alphaSelected_empty :
    alphaSelectedUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) 4 ∅ =
    ((chainSubsetsFinset ((Finset.univ : Finset {s : Finset (Fin 7) // K2 s}).filter
      (fun x => x.val.card ∈ (∅ : Finset ℕ)))).filter
      (fun C => C.image (fun x => x.val.card) = ∅ ∧ C.card = (∅ : Finset ℕ).card)).card := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem alphaSelected_two :
    alphaSelectedUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) 4 {2} =
    ((chainSubsetsFinset ((Finset.univ : Finset {s : Finset (Fin 7) // K2 s}).filter
      (fun x => x.val.card ∈ ({2} : Finset ℕ)))).filter
      (fun C => C.image (fun x => x.val.card) = {2} ∧ C.card = ({2} : Finset ℕ).card)).card := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem alphaSelected_three :
    alphaSelectedUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) 4 {3} =
    ((chainSubsetsFinset ((Finset.univ : Finset {s : Finset (Fin 7) // K2 s}).filter
      (fun x => x.val.card ∈ ({3} : Finset ℕ)))).filter
      (fun C => C.image (fun x => x.val.card) = {3} ∧ C.card = ({3} : Finset ℕ).card)).card := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem alphaSelected_four :
    alphaSelectedUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) 4 {4} =
    ((chainSubsetsFinset ((Finset.univ : Finset {s : Finset (Fin 7) // K2 s}).filter
      (fun x => x.val.card ∈ ({4} : Finset ℕ)))).filter
      (fun C => C.image (fun x => x.val.card) = {4} ∧ C.card = ({4} : Finset ℕ).card)).card := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem alphaSelected_two_four :
    alphaSelectedUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) 4 {2,4} =
    ((chainSubsetsFinset ((Finset.univ : Finset {s : Finset (Fin 7) // K2 s}).filter
      (fun x => x.val.card ∈ ({2,4} : Finset ℕ)))).filter
      (fun C => C.image (fun x => x.val.card) = {2,4} ∧ C.card = ({2,4} : Finset ℕ).card)).card := by decide +kernel
private theorem alphaSelected_all :
    ∀ T ∈ (Finset.Icc 2 4).powerset.filter isolated,
    alphaSelectedUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) 4 T =
    ((chainSubsetsFinset ((Finset.univ : Finset {s : Finset (Fin 7) // K2 s}).filter
      (fun x => x.val.card ∈ T))).filter
      (fun C => C.image (fun x => x.val.card) = T ∧ C.card = T.card)).card := by
  intro T hT
  rw [isolated_four] at hT
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl
  · exact alphaSelected_empty
  · exact alphaSelected_two
  · exact alphaSelected_three
  · exact alphaSelected_four
  · exact alphaSelected_two_four
private theorem alpha_P2_using (T : Finset ℕ)
    (hT : T ∈ (Finset.Icc 2 4).powerset.filter isolated) :
    alpha {s : Finset (Fin 7) // K2 s} 4 T =
    alphaUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) T := by
  rw [alpha_card, alphaUsing_chainSubsets]
  exact alphaSelected_all T hT
private theorem H_card : H {s : Finset (Fin 7) // K2 s} 4 =
    HUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) 4 := by
  classical
  unfold H HUsing
  apply Finset.sum_congr rfl
  intro S hS
  have hb : beta {s : Finset (Fin 7) // K2 s} 4 S =
      betaUsing {s : Finset (Fin 7) // K2 s} (fun x => x.val.card) S := by
    unfold beta betaUsing
    apply Finset.sum_congr rfl
    intro T hT
    have hTS := Finset.mem_powerset.mp hT
    have hTrange : T ⊆ Finset.Icc 2 4 :=
      hTS.trans (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
    have hTiso : isolated T := fun i hi hip =>
      (Finset.mem_filter.mp hS).2 i (hTS hi) (hTS hip)
    rw [alpha_P2_using T (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTrange, hTiso⟩)]
  rw [hb]
private theorem H_P2 : H {s : Finset (Fin 7) // K2 s} 4 = X^4 + 23*X^3 + 43*X^2 + 23*X + 1 := by
  classical
  rw [H_card]
  unfold HUsing
  rw [isolated_four, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [Finset.sum_insert, Finset.sum_singleton, beta0_card, beta2_card,
    beta3_card, beta4_card, beta24_card]
  ring
open Polynomial
private noncomputable def a : ℝ := (23 - Real.sqrt 365) / 2
private noncomputable def b : ℝ := (23 + Real.sqrt 365) / 2
private noncomputable def z : ℂ := (-(a : ℂ) + Complex.I * (Real.sqrt (4 - a^2) : ℂ)) / 2
private theorem a_bounds : 0 < a ∧ a < 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 365)
  have hnn := Real.sqrt_nonneg (365 : ℝ)
  have h19 : 19 < Real.sqrt 365 := by nlinarith
  have h23 : Real.sqrt 365 < 23 := by nlinarith
  constructor <;> unfold a <;> linarith
private theorem a_add_b : a + b = 23 := by unfold a b; ring
private theorem a_mul_b : a * b = 41 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 365)
  unfold a b
  nlinarith
private theorem quartic_factorization :
    ((X^4 + 23*X^3 + 43*X^2 + 23*X + 1 : Polynomial ℤ).map (Int.castRingHom ℝ)) =
    (X^2 + C a * X + 1) * (X^2 + C b * X + 1) := by
  have hs := congrArg (C : ℝ → Polynomial ℝ) a_add_b
  have hp := congrArg (C : ℝ → Polynomial ℝ) a_mul_b
  simp only [C_add, C_mul, C_ofNat] at hs hp
  norm_num
  linear_combination -X^3 * hs - X^2 * hp - X * hs
private theorem z_quadratic : z^2 + (a : ℂ) * z + 1 = 0 := by
  have hpos : 0 < 4 - a^2 := by
    have hb := a_bounds
    nlinarith
  have hsq := Real.sq_sqrt hpos.le
  simp only [pow_two] at hsq
  have hdisc : discrim (1 : ℂ) (a : ℂ) 1 =
      (Complex.I * (Real.sqrt (4 - a^2) : ℂ)) *
      (Complex.I * (Real.sqrt (4 - a^2) : ℂ)) := by
    apply Complex.ext
    · simp [discrim, Complex.mul_re, Complex.mul_im, pow_two]
      nlinarith
    · simp [discrim, Complex.mul_re, Complex.mul_im, pow_two]
  have h := (quadratic_eq_zero_iff (by norm_num : (1 : ℂ) ≠ 0) hdisc z).mpr
    (Or.inl (by simp [z]))
  simpa only [one_mul, ← pow_two] using h
private theorem z_im_ne : z.im ≠ 0 := by
  have hpos : 0 < 4 - a^2 := by
    have hb := a_bounds
    nlinarith
  have hs : 0 < Real.sqrt (4 - a^2) := Real.sqrt_pos.mpr hpos
  have hz : z.im = Real.sqrt (4 - a^2) / 2 := by
    simp [z, Complex.div_ofNat, Complex.mul_im]
  rw [hz]
  exact ne_of_gt (div_pos hs (by norm_num))
open Polynomial
private theorem H_P2_factorization : (H {s : Finset (Fin 7) // K2 s} 4).map (Int.castRingHom ℝ) =
    (X^2 + C a * X + 1) * (X^2 + C b * X + 1) := by
  rw [H_P2]
  exact quartic_factorization
private theorem H_P2_root :
    ((H {s : Finset (Fin 7) // K2 s} 4).map (Int.castRingHom ℂ)).eval z = 0 := by
  have he := congrArg (fun p : Polynomial ℝ =>
    (p.map Complex.ofRealHom).eval z) H_P2_factorization
  have hh : Complex.ofRealHom.comp (Int.castRingHom ℝ) = Int.castRingHom ℂ := by
    ext i
    simp
  rw [Polynomial.map_map, hh] at he
  rw [he]
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_one,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  simp only [Complex.ofRealHom_eq_coe]
  rw [z_quadratic]
  simp
theorem result : ¬ claim := by
  intro h
  have hh : (algebraMap ℝ ℂ).comp (Int.castRingHom ℝ) = Int.castRingHom ℂ := by
    ext i
    simp
  have hz : (((H {s : Finset (Fin 7) // K2 s} 4).map (Int.castRingHom ℝ)).map
      (algebraMap ℝ ℂ)).eval z = 0 := by
    rw [Polynomial.map_map, hh]
    exact H_P2_root
  exact z_im_ne (h {s : Finset (Fin 7) // K2 s} 4 P2_simplicial z hz)
end D5.S3.Zeros.SimplicialPosetChowRefutation
