/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Whole geometry fibers count all ordered sources and pure substitution entrances. -/

import D5.S3.Combinatorics.Partitions.WordPartitionInverse
import D5.S3.Arith.FibonacciAtomic.SourceTransportCentralizer
import D5.S1.Words.Palindromes.GoldenPalindromicPrefixComplete
import Mathlib.Data.Vector.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio

open GenealogicalFiberTransport (Source substitution composition assemble decompose
  sourceEquiv labelsEquiv indexedEquiv TreeLabels)
open D5.S3.Combinatorics.Partitions.PaddedWordPartition
open D5.S3.Combinatorics.Partitions.WordPartitionInverse
  (wd wd_nonempty leftComb leftComb_word pair_count_bound)
open D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge (binary_letter_counts_length)

/-- All nonempty words with this exact joint geometry, with no word-family restriction. -/
def WordFiber (g : Five) := {w : List Bool // w ≠ [] ∧ G w = g}
/-- All ordered binary sources with this exact same-word geometry. -/
def TreeFiber (g : Five) := {t : Source // G (wd t) = g}
/-- All current/source/depth triples, with no bound imposed on legal depths. -/
def EntranceFiber (g : Five) :=
  {p : Source × Source × ℕ // G (wd p.1) = g ∧ substitution^[p.2.2] p.2.1 = p.1}

/-- The leaf count read from the actual endpoint. Nonactual candidates remain permitted. -/
def N (g : Five) : ℕ := ⌊g.u + g.v⌋₊

def L (g : Five) : Five :=
  ⟨g.v, g.u + g.v, -g.d - g.v, g.v - g.f, -g.v - 3*g.d - g.e - g.f⟩
def Linv (g : Five) : Five :=
  ⟨g.v-g.u, g.u, -g.d-g.u, g.u+3*g.d+g.e-g.f, g.u-g.e⟩
def letter (b : Bool) : List Bool := if b then [false] else [false,true]
def sigma (w : List Bool) : List Bool := w.flatMap letter

private theorem inverse_left (g : Five) : Linv (L g) = g := by
  apply Five.ext
  · dsimp [L,Linv]; ring
  · rfl
  · dsimp [L,Linv]; ring
  · dsimp [L,Linv]; ring
  · dsimp [L,Linv]; ring
private theorem inverse_right (g : Five) : L (Linv g) = g := by
  apply Five.ext
  · rfl
  · dsimp [L,Linv]; ring
  · dsimp [L,Linv]; ring
  · dsimp [L,Linv]; ring
  · dsimp [L,Linv]; ring

private theorem wd_mul (s t : Source) : wd (.mul s t) = wd s ++ wd t := by
  simp [wd, map_mul]

private theorem wd_composition (t : Source) :
    ((wd t).count true, (wd t).count false) = composition t := by
  induction t with
  | of b => cases b <;> rfl
  | mul s t hs ht =>
    rw [wd_mul, composition, List.count_append, List.count_append]
    exact congrArg₂ (fun a b : ℕ × ℕ => a+b) hs ht

private theorem wd_length (t : Source) : (wd t).length = t.length := by
  induction t with
  | of b => rfl
  | mul s t hs ht => simp only [wd_mul, List.length_append, FreeMagma.length, hs, ht]

private theorem endpoint (w : List Bool) :
    (G w).u = w.count true ∧ (G w).v = w.count false := by
  rw [all_word_direct]; exact ⟨rfl,rfl⟩

private theorem word_length (g : Five) (w : WordFiber g) : w.val.length = N g := by
  have he := endpoint w.val
  rw [w.property.2] at he
  unfold N
  rw [he.1, he.2, ← Nat.cast_add, binary_letter_counts_length, Nat.floor_natCast]

private theorem tree_length (g : Five) (t : TreeFiber g) : t.val.length = N g := by
  rw [← wd_length]
  exact word_length g ⟨wd t.val, wd_nonempty _, t.property⟩

instance wordFinite (g : Five) : Finite (WordFiber g) := by
  let : Finite {w : List Bool // w.length = N g} :=
    (List.finite_length_eq Bool (N g)).to_subtype
  exact Finite.of_injective
    (fun w : WordFiber g => (⟨w.val, word_length g w⟩ : {w : List Bool // w.length = N g}))
    (fun _ _ h => Subtype.ext
      (congrArg (fun w : {w : List Bool // w.length = N g} => w.val) h))

private theorem bounded_tree_finite (n : ℕ) : Finite {t : Source // t.length ≤ n} := by
  let f : {t : Source // t.length ≤ n} →
      Σ a : Fin (n+1), Σ b : Fin (n+1), GenealogicalFiberTransport.Fiber (a.val,b.val) := fun t =>
    ⟨⟨(composition t.val).1, by
        have h := wd_composition t.val
        have hl := binary_letter_counts_length (wd t.val)
        rw [wd_length] at hl
        have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        dsimp only at h₁ h₂
        omega⟩,
     ⟨(composition t.val).2, by
        have h := wd_composition t.val
        have hl := binary_letter_counts_length (wd t.val)
        rw [wd_length] at hl
        have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        dsimp only at h₁ h₂
        omega⟩,
     ⟨t.val, Prod.ext rfl rfl⟩⟩
  exact Finite.of_injective f (fun _ _ h => by
    have hh := congrArg (fun p => p.2.2.val) h
    exact Subtype.ext hh)

instance treeFinite (g : Five) : Finite (TreeFiber g) := by
  let := bounded_tree_finite (N g)
  exact Finite.of_injective
    (fun t : TreeFiber g => (⟨t.val, (tree_length g t).le⟩ : {t : Source // t.length ≤ N g}))
    (fun _ _ h => Subtype.ext
      (congrArg (fun t : {t : Source // t.length ≤ N g} => t.val) h))

private theorem composition_transport (t : Source) :
    composition (substitution t) = GraftAffineClosure.step (composition t) :=
  (GenealogicalFiberTransport.fiberMap (composition t) 1 ⟨t,rfl⟩).property

private theorem substitution_length (t : Source) :
    t.length ≤ (substitution t).length := by
  have h := composition_transport t
  have hw := wd_composition t
  have hw' := wd_composition (substitution t)
  have hlen := binary_letter_counts_length (wd t)
  have hlen' := binary_letter_counts_length (wd (substitution t))
  rw [wd_length] at hlen hlen'
  rw [h] at hw'
  have h₁ := congrArg Prod.fst hw'
  have h₂ := congrArg Prod.snd hw'
  have h₃ := congrArg Prod.fst hw
  have h₄ := congrArg Prod.snd hw
  dsimp [GraftAffineClosure.step] at h₁ h₂ h₃ h₄
  omega

private theorem iterate_length (k : ℕ) (t : Source) :
    t.length ≤ (substitution^[k] t).length := by
  induction k with
  | zero => exact le_rfl
  | succ k hk =>
    rw [Function.iterate_succ_apply']
    exact hk.trans (substitution_length _)

/-- A coarse cutoff proved for every actual entrance, including the same-size alpha/beta step. -/
private theorem entrance_cutoff (k : ℕ) (t : Source) :
    k < 2 * (substitution^[k] t).length := by
  have hw (s : Source) : (composition s).1 + (composition s).2 = s.length := by
    have h := wd_composition s
    have hl := binary_letter_counts_length (wd s)
    rw [wd_length] at hl
    rw [← h]
    exact hl
  have growth : ∀ k : ℕ, k+1 ≤ (composition (substitution^[k] t)).1 +
      2*(composition (substitution^[k] t)).2 := by
    intro k
    induction k with
    | zero =>
      have hp := t.length_pos
      have h := hw t
      simp only [Function.iterate_zero_apply]
      omega
    | succ k hk =>
      rw [Function.iterate_succ_apply', composition_transport]
      have hp := (substitution^[k] t).length_pos
      have h := hw (substitution^[k] t)
      dsimp [GraftAffineClosure.step]
      omega
  have h := growth k
  have hl := hw (substitution^[k] t)
  omega

instance entranceFinite (g : Five) : Finite (EntranceFiber g) := by
  let := bounded_tree_finite (N g)
  let f : EntranceFiber g →
      TreeFiber g × {t : Source // t.length ≤ N g} × Fin (2*N g) := fun p =>
    ⟨⟨p.val.1,p.property.1⟩,
     ⟨p.val.2.1, by
        have h := iterate_length p.val.2.2 p.val.2.1
        rw [p.property.2] at h
        exact h.trans (tree_length g ⟨p.val.1,p.property.1⟩).le⟩,
     ⟨p.val.2.2, by
        have h := entrance_cutoff p.val.2.2 p.val.2.1
        rw [p.property.2, tree_length g ⟨p.val.1,p.property.1⟩] at h
        exact h⟩⟩
  exact Finite.of_injective f (fun _ _ h => by
    apply Subtype.ext
    exact Prod.ext (congrArg (fun q => q.1.val) h)
      (Prod.ext (congrArg (fun q => q.2.1.val) h) (congrArg (fun q => q.2.2.val) h)))

/-- Literal finite cardinalities, defined only after proving actual finiteness. -/
def m (g : Five) : ℕ := Nat.card (WordFiber g)
def M (g : Five) : ℕ := Nat.card (TreeFiber g)
def H (g : Five) : ℕ := Nat.card (EntranceFiber g)

private theorem sigma_geometry (w : List Bool) : G (sigma w) = L (G w) := by
  rw [sigma, direct_accumulator, List.foldl_flatMap, direct_accumulator]
  have h := List.foldl_hom L (g₁ := U)
    (g₂ := fun g c => (letter c).foldl U g) (l := w) (init := zeroFive)
    (by intro g c; cases c <;> apply Five.ext <;> simp [letter,L,U] <;> ring)
  have hz : L zeroFive = zeroFive := by apply Five.ext <;> simp [L,zeroFive]
  simpa only [hz] using h

private theorem wd_substitution (t : Source) : wd (substitution t) = sigma (wd t) := by
  induction t with
  | of b => cases b <;> rfl
  | mul s t hs ht =>
    change wd (.mul (substitution s) (substitution t)) = _
    rw [wd_mul, hs, ht, wd_mul]
    exact (List.flatMap_append).symm

private theorem tree_geometry (t : Source) : G (wd (substitution t)) = L (G (wd t)) := by
  rw [wd_substitution, sigma_geometry]

private theorem sigma_injective : Function.Injective sigma := by
  have conjugacy (w : List Bool) : sigma w =
      (((w.map Bool.not).flatMap D5.S0.Tower.GoldenGapWord.subst).map Bool.not) := by
    rw [List.map_flatMap, List.flatMap_map]
    apply congrArg (fun f : Bool → List Bool => w.flatMap f)
    funext c
    cases c <;> rfl
  intro w z h
  rw [conjugacy, conjugacy] at h
  have hi : Function.Injective (fun w : List Bool => w.map Bool.not) :=
    List.map_injective_iff.mpr Bool.not_injective
  exact hi (D5.S1.Words.flatMap_subst_injective (hi h))

private theorem sigma_nonempty (w : List Bool) (hw : w ≠ []) : sigma w ≠ [] := by
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons c w => cases c <;> simp [sigma,letter]

private theorem word_injection (g : Five) : m (Linv g) ≤ m g := by
  let f : WordFiber (Linv g) → WordFiber g := fun w =>
    ⟨sigma w.val, sigma_nonempty _ w.property.1, by
      rw [sigma_geometry, w.property.2, inverse_right]⟩
  exact Nat.card_le_card_of_injective f (fun _ _ h =>
    Subtype.ext (sigma_injective (congrArg Subtype.val h)))

private def labelsWordEquiv (s : BinaryTree Unit) :
    TreeLabels s ≃ {w : List Bool // w.length = s.numLeaves} :=
  (labelsEquiv s).trans (Equiv.vectorEquivFin Bool s.numLeaves).symm

private theorem assemble_word (s : BinaryTree Unit) (x : TreeLabels s) :
    wd (assemble s x) = List.ofFn (labelsEquiv s x) := by
  induction s with
  | nil => change [x] = List.ofFn (fun _ : Fin 1 => x); simp
  | node u l r hl hr =>
    rcases x with ⟨a,b⟩
    change wd (.mul (assemble l a) (assemble r b)) =
      List.ofFn (Fin.append (labelsEquiv l a) (labelsEquiv r b))
    rw [wd_mul, hl, hr, List.ofFn_fin_append]

private theorem labelsWord_spec (s : BinaryTree Unit) (x : TreeLabels s) :
    (labelsWordEquiv s x).val = wd (assemble s x) := by
  change (List.Vector.ofFn (labelsEquiv s x)).toList = _
  rw [List.Vector.toList_ofFn, assemble_word]

private def wordedEquiv :
    Source ≃ Σ s : BinaryTree Unit, {w : List Bool // w.length = s.numLeaves} :=
  sourceEquiv.trans (Equiv.sigmaCongrRight labelsWordEquiv)

private theorem worded_spec (t : Source) : (wordedEquiv t).2.val = wd t := by
  change (labelsWordEquiv (sourceEquiv t).1 (sourceEquiv t).2).val = _
  rw [labelsWord_spec]
  exact congrArg wd (sourceEquiv.symm_apply_apply t)

/-- This product uses every ordered shape and the whole actual word fiber. -/
private def geometryEquiv (g : Five) (hg : 0 < N g) :
    TreeFiber g ≃ BinaryTree.treesOfNumNodesEq (N g-1) × WordFiber g := by
  let e := wordedEquiv.subtypeEquiv
    (p := fun t => G (wd t) = g)
    (q := fun p => G p.2.val = g)
    (fun t => by rw [worded_spec])
  refine e.trans ?_
  refine
    { toFun := fun p => ⟨⟨p.val.1, ?_⟩, ⟨p.val.2.val, ?_, p.property⟩⟩
      invFun := fun p => ⟨⟨p.1.val, ⟨p.2.val, ?_⟩⟩, p.2.property.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply BinaryTree.mem_treesOfNumNodesEq.mpr
    have hne : p.val.2.val ≠ [] := by
      intro he
      have hlen := p.val.2.property
      rw [he, List.length_nil, BinaryTree.numLeaves_eq_numNodes_succ] at hlen
      omega
    have hlen := word_length g ⟨p.val.2.val,hne,p.property⟩
    change p.val.2.val.length = N g at hlen
    have hs := p.val.1.numLeaves_eq_numNodes_succ
    have hv := p.val.2.property
    omega
  · intro he
    have hlen := p.val.2.property
    rw [he, List.length_nil, BinaryTree.numLeaves_eq_numNodes_succ] at hlen
    omega
  · have hs := BinaryTree.mem_treesOfNumNodesEq.mp p.1.property
    rw [word_length g p.2, BinaryTree.numLeaves_eq_numNodes_succ, hs]
    omega
  · intro p
    rfl
  · intro p
    rfl

private theorem tree_card (g : Five) (hg : 0 < N g) :
    M g = catalan (N g-1) * m g := by
  rw [M, Nat.card_congr (geometryEquiv g hg), Nat.card_prod]
  simp only [Nat.card_eq_fintype_card,
    Fintype.card_coe, BinaryTree.treesOfNumNodesEq_card_eq_catalan]
  rfl

/-- The depth-zero summand and all positive-depth entrances are disjoint and exhaustive. -/
private def entranceSplit (g : Five) :
    EntranceFiber g ≃ TreeFiber g ⊕ EntranceFiber (Linv g) where
  toFun p := match hk : p.val.2.2 with
    | 0 => .inl ⟨p.val.1,p.property.1⟩
    | k+1 => .inr ⟨(substitution^[k] p.val.2.1,p.val.2.1,k), by
        have he : substitution (substitution^[k] p.val.2.1) = p.val.1 := by
          simpa only [hk, Function.iterate_succ_apply'] using p.property.2
        constructor
        · rw [← inverse_left (G (wd (substitution^[k] p.val.2.1))),
            ← tree_geometry, he, p.property.1]
        · rfl⟩
  invFun p := match p with
    | .inl t => ⟨(t.val,t.val,0), t.property,rfl⟩
    | .inr p => ⟨(substitution p.val.1,p.val.2.1,p.val.2.2+1), by
        constructor
        · rw [tree_geometry,p.property.1,inverse_right]
        · rw [Function.iterate_succ_apply',p.property.2]⟩
  left_inv p := by
    rcases p with ⟨⟨y,x,k⟩,hg,he⟩
    cases k with
    | zero =>
      apply Subtype.ext
      change (y,y,0) = (y,x,0)
      simpa only [Function.iterate_zero_apply] using
        congrArg (fun t : Source => (y,t,0)) he.symm
    | succ k =>
      apply Subtype.ext
      change (substitution (substitution^[k] x),x,k+1) = (y,x,k+1)
      exact congrArg (fun t : Source => (t,x,k+1))
        (by simpa only [Function.iterate_succ_apply'] using he)
  right_inv p := by
    cases p with
    | inl t => rfl
    | inr p =>
      apply congrArg Sum.inr
      apply Subtype.ext
      change (substitution^[p.val.2.2] p.val.2.1,p.val.2.1,p.val.2.2) = p.val
      rw [p.property.2]

private theorem entrance_recursion (g : Five) : H g = M g + H (Linv g) := by
  exact (Nat.card_congr (entranceSplit g)).trans Nat.card_sum

/-- Actual cardinal recursion and the injection on complete same-source word fibers. -/
theorem actual_fiber_counting (g : Five) :
    (0 < N g → M g = catalan (N g-1) * m g) ∧
    H g = M g + H (Linv g) ∧ m (Linv g) ≤ m g ∧ M g ≤ H g := by
  have hr := entrance_recursion g
  exact ⟨tree_card g,hr,word_injection g,by omega⟩

/-- The exact geometry of a pure word, used as an entire-fiber example. -/
def pure (b : Bool) (n : ℕ) : Five :=
  if b then ⟨n,0,0,0,0⟩ else ⟨0,n,0,0,0⟩

private theorem pure_geometry (b : Bool) (n : ℕ) : G (List.replicate n b) = pure b n := by
  induction n with
  | zero => cases b <;> apply Five.ext <;> simp [pure,G_nil,zeroFive]
  | succ n ih =>
    rw [List.replicate_succ', G_append, ih]
    cases b <;> apply Five.ext <;> simp [pure,U,Nat.cast_add]

private theorem pure_length (b : Bool) (n : ℕ) : N (pure b n) = n := by
  cases b <;> simp [N,pure]

private theorem pure_unique (b : Bool) (n : ℕ) (w : WordFiber (pure b n)) :
    w.val = List.replicate n b := by
  have he := endpoint w.val
  rw [w.property.2] at he
  have hl := word_length (pure b n) w
  rw [pure_length] at hl
  have hc : w.val.count b = n := by
    cases b with
    | false => exact_mod_cast (by simpa [pure] using he.2.symm)
    | true => exact_mod_cast (by simpa [pure] using he.1.symm)
  have h := List.replicate_count_eq_of_count_eq_length (hc.trans hl.symm)
  rw [hc] at h
  exact h.symm

private theorem pure_word_card (b : Bool) (n : ℕ) (hn : 0 < n) : m (pure b n) = 1 := by
  let e : WordFiber (pure b n) ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨List.replicate n b, by
        intro h
        have hh := congrArg List.length h
        simp only [List.length_replicate,List.length_nil] at hh
        omega, pure_geometry b n⟩
      left_inv := fun w => Subtype.ext (pure_unique b n w).symm
      right_inv := fun u => Subsingleton.elim _ u }
  exact (Nat.card_congr e).trans (by simp)

private theorem empty_counts (g : Five) (he : ¬ Nonempty (TreeFiber g)) :
    M g = 0 ∧ H g = 0 := by
  let : IsEmpty (TreeFiber g) := not_nonempty_iff.mp he
  let : IsEmpty (EntranceFiber g) := ⟨fun p =>
    he ⟨⟨p.val.1,p.property.1⟩⟩⟩
  simp [M,H]

private theorem negative_endpoint (g : Five) (he : g.u < 0 ∨ g.v < 0) :
    ¬ Nonempty (TreeFiber g) := by
  rintro ⟨t⟩
  have h := endpoint (wd t.val)
  rw [t.property] at h
  rcases he with he | he
  · have hn : 0 ≤ g.u := h.1 ▸ Nat.cast_nonneg _
    linarith
  · have hn : 0 ≤ g.v := h.2 ▸ Nat.cast_nonneg _
    linarith

private theorem pure_counts (n : ℕ) (hn : 0 < n) :
    M (pure true n) = catalan (n-1) ∧ H (pure true n) = M (pure true n) ∧
    M (pure false n) = catalan (n-1) ∧ H (pure false n) = 2*M (pure false n) := by
  have ht := tree_card (pure true n) (by simpa [pure_length] using hn)
  have hf := tree_card (pure false n) (by simpa [pure_length] using hn)
  rw [pure_length, pure_word_card true n hn, mul_one] at ht
  rw [pure_length, pure_word_card false n hn, mul_one] at hf
  have ha : H (Linv (pure true n)) = 0 :=
    (empty_counts _ (negative_endpoint _ (Or.inl (by
      dsimp [Linv,pure]
      have hp : 0 < (n : ℝ) := by exact_mod_cast hn
      linarith)))).2
  have hinv : Linv (pure false n) = pure true n := by
    apply Five.ext <;> simp [Linv,pure]
  have hrt := entrance_recursion (pure true n)
  rw [ha,add_zero] at hrt
  have hrf := entrance_recursion (pure false n)
  rw [hinv, hrt, ht, ← hf] at hrf
  exact ⟨ht,hrt,hf,by omega⟩

private theorem catalan_double (j : ℕ) (hj : 1 ≤ j) : 2 * catalan j ≤ catalan (j + 1) := by
  rw [catalan_succ]
  have hne : (0 : Fin (j + 1)) ≠ ⟨j, by omega⟩ := by
    intro h
    have hval := congrArg Fin.val h
    dsimp at hval
    omega
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun i : Fin (j + 1) => catalan i * catalan (j - i))
    (show {(0 : Fin (j + 1)), ⟨j, by omega⟩} ⊆ Finset.univ from Finset.subset_univ _)
    (by intros; exact Nat.zero_le _)
  simpa [hne, catalan_zero, two_mul] using h

private theorem catalan_monotone : Monotone catalan := by
  apply monotone_nat_of_le_succ
  intro j
  cases j with
  | zero => simp [catalan_zero,catalan_one]
  | succ j => have h := catalan_double (j+1) (by omega); omega

private def RatioBound (n a h : ℕ) : Prop :=
  if n = 2 then h ≤ 3*a else if n = 3 then 2*h ≤ 5*a else h ≤ 2*a

private theorem sharp_induction (n : ℕ) : ∀ g : Five, N g = n → RatioBound n (M g) (H g) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro g hN
    by_cases hg : Nonempty (TreeFiber g)
    · obtain ⟨t⟩ := hg
      let w : WordFiber g := ⟨wd t.val,wd_nonempty _,t.property⟩
      let a := w.val.count true
      let b := w.val.count false
      have ep := endpoint w.val
      rw [w.property.2] at ep
      have hn : 0 < n := by
        have h := t.val.length_pos
        rw [tree_length g t, hN] at h
        exact h
      have hab : a+b = n := by
        have hl := binary_letter_counts_length w.val
        rw [word_length g w, hN] at hl
        exact hl
      by_cases ha : a = 0
      · have hw : w.val = List.replicate n false := by
          have hc : w.val.count false = w.val.length := by
            have h := binary_letter_counts_length w.val
            change a+b = w.val.length at h
            omega
          have h := List.replicate_count_eq_of_count_eq_length hc
          have hb : w.val.count false = n := by change b = n; omega
          rw [hb] at h
          exact h.symm
        have hgp : g = pure false n := by rw [← w.property.2, hw, pure_geometry]
        have hp := (pure_counts n hn).2.2.2
        rw [hgp]
        unfold RatioBound
        split_ifs <;> omega
      · by_cases hpre : Nonempty (TreeFiber (Linv g))
        · obtain ⟨s⟩ := hpre
          have hp := endpoint (wd s.val)
          rw [s.property] at hp
          have hab' : a ≤ b := by
            have hs : 0 ≤ (Linv g).u := hp.1 ▸ Nat.cast_nonneg _
            change 0 ≤ g.v-g.u at hs
            rw [ep.1,ep.2] at hs
            exact_mod_cast (by linarith : (a : ℝ) ≤ b)
          have hb : 0 < b := by omega
          have hbN : b < n := by omega
          have hpreN : N (Linv g) = b := by
            unfold N Linv
            dsimp only
            rw [sub_add_cancel,ep.2,Nat.floor_natCast]
          have hi := ih b hbN (Linv g) hpreN
          have hc := (actual_fiber_counting g).1 (by omega)
          have hd := (actual_fiber_counting (Linv g)).1 (by omega)
          rw [hN] at hc
          rw [hpreN] at hd
          have hm := (actual_fiber_counting g).2.2.1
          have hr := (actual_fiber_counting g).2.1
          by_cases hn2 : n = 2
          · have hb1 : b = 1 := by omega
            rw [hb1] at hi hd
            norm_num [RatioBound,catalan_zero] at hi hd
            have hsmall : M (Linv g) ≤ M g := by
              rw [hc,hn2,hd]
              simpa [catalan_one] using hm
            rw [RatioBound,if_pos hn2]
            omega
          · by_cases hn3 : n = 3
            · have hb2 : b = 2 := by omega
              rw [hb2] at hi hd
              norm_num [RatioBound,catalan_one] at hi hd
              have hsmall : 2*M (Linv g) ≤ M g := by
                rw [hc,hn3,hd]
                simpa [catalan_two] using Nat.mul_le_mul_left 2 hm
              rw [RatioBound,if_neg hn2,if_pos hn3]
              omega
            · have hn4 : 4 ≤ n := by omega
              have hcat : 5 ≤ catalan (n-1) := by
                simpa only [catalan_three] using catalan_monotone (show 3 ≤ n-1 by omega)
              have htail : H (Linv g) ≤ M g := by
                by_cases hb4 : 4 ≤ b
                · have hi' : H (Linv g) ≤ 2*M (Linv g) := by
                    simpa [RatioBound,show b ≠ 2 by omega,show b ≠ 3 by omega] using hi
                  have hcata : 2*catalan (b-1) ≤ catalan (n-1) :=
                    (catalan_double (b-1) (by omega)).trans
                      (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ b)] using
                        catalan_monotone (show b ≤ n-1 by omega))
                  have hmul := Nat.mul_le_mul hcata hm
                  rw [hc]
                  rw [hd] at hi'
                  nlinarith
                · have hb3 : b ≤ 3 := by omega
                  interval_cases b
                  · norm_num [RatioBound,catalan_zero] at hi hd
                    have hmul := Nat.mul_le_mul (show 2 ≤ catalan (n-1) by omega) hm
                    rw [hc]
                    rw [hd] at hi
                    nlinarith
                  · norm_num [RatioBound,catalan_one] at hi hd
                    have hmul := Nat.mul_le_mul (show 3 ≤ catalan (n-1) by omega) hm
                    rw [hc]
                    rw [hd] at hi
                    nlinarith
                  · norm_num [RatioBound,catalan_two] at hi hd
                    have hmul := Nat.mul_le_mul hcat hm
                    rw [hc]
                    rw [hd] at hi
                    nlinarith
              rw [RatioBound,if_neg hn2,if_neg hn3]
              omega
        · have he := (empty_counts _ hpre).2
          have hr := entrance_recursion g
          rw [he,add_zero] at hr
          rw [hr]
          unfold RatioBound
          split_ifs <;> omega
    · obtain ⟨hm,hh⟩ := empty_counts g hg
      simp [RatioBound,hm,hh]

/-- Uniform estimates on literal whole actual fibers, with an exact three-leaf rational bound. -/
theorem uniform_actual_entrance_estimate (g : Five) :
    M g ≤ H g ∧
    (N g = 1 → H g ≤ 2*M g) ∧
    (N g = 2 → H g ≤ 3*M g) ∧
    (N g = 3 → 2*H g ≤ 5*M g) ∧
    (4 ≤ N g → H g ≤ 2*M g) ∧ H g ≤ 3*M g := by
  have hb := sharp_induction (N g) g rfl
  have hlo := (actual_fiber_counting g).2.2.2
  refine ⟨hlo,?_,?_,?_,?_,?_⟩
  · intro hn; simpa [RatioBound,hn] using hb
  · intro hn; simpa [RatioBound,hn] using hb
  · intro hn; simpa [RatioBound,hn] using hb
  · intro hn
    simpa [RatioBound,show N g ≠ 2 by omega,show N g ≠ 3 by omega] using hb
  · unfold RatioBound at hb
    split_ifs at hb <;> omega

/-- The sharp ratio at each positive leaf count. -/
def B (n : ℕ) : ℝ := if n = 2 then 3 else if n = 3 then 5/2 else 2
/-- The exceptional two-leaf full-fiber geometry. -/
def ba : Five := ⟨1,1,-1,1,-1⟩
/-- The exceptional three-leaf full-fiber geometry. -/
def bab : Five := ⟨1,2,0,2,2⟩

private theorem ba_geometry : G [false,true] = ba := by
  rw [direct_list_fan]
  norm_num [ba,rows,squareRows,oddRows,
    D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge.scatteredTrueFalseCount]
private theorem bab_geometry : G [false,true,false] = bab := by
  rw [direct_list_fan]
  norm_num [bab,rows,squareRows,oddRows,
    D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge.scatteredTrueFalseCount]

private theorem ba_unique (w : WordFiber ba) : w.val = [false,true] := by
  have hl : w.val.length = 2 := by have h := word_length ba w; norm_num [N,ba] at h; exact h
  obtain ⟨a,b,he⟩ := List.length_eq_two.mp hl
  have hu := congrArg Five.u w.property.2
  have hd := congrArg Five.d w.property.2
  rw [he, direct_list_fan] at hu hd
  rw [he]
  cases a <;> cases b <;>
    simp_all [ba,D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge.scatteredTrueFalseCount]

private theorem bab_unique (w : WordFiber bab) : w.val = [false,true,false] := by
  have hl : w.val.length = 3 := by have h := word_length bab w; norm_num [N,bab] at h; exact h
  obtain ⟨a,b,c,he⟩ := List.length_eq_three.mp hl
  have hu := congrArg Five.u w.property.2
  have hd := congrArg Five.d w.property.2
  rw [he, direct_list_fan] at hu hd
  rw [he]
  cases a <;> cases b <;> cases c <;>
    simp_all [bab,
      D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge.scatteredTrueFalseCount] <;>
      norm_num at *

private theorem singleton_word_card (g : Five) (w : WordFiber g)
    (hu : ∀ z : WordFiber g, z.val = w.val) : m g = 1 := by
  let e : WordFiber g ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => w
      left_inv := fun z => Subtype.ext (hu z).symm
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (by simp)

private theorem exceptional_counts :
    m ba = 1 ∧ M ba = 1 ∧ H ba = 3 ∧ m bab = 1 ∧ M bab = 2 ∧ H bab = 5 := by
  have hba := singleton_word_card ba ⟨[false,true],by simp,ba_geometry⟩ ba_unique
  have hbab := singleton_word_card bab ⟨[false,true,false],by simp,bab_geometry⟩ bab_unique
  have tba := tree_card ba (by norm_num [N,ba])
  have tbab := tree_card bab (by norm_num [N,bab])
  rw [show N ba = 2 by norm_num [N,ba],show 2-1 = (1 : ℕ) by omega,
    catalan_one,hba,mul_one] at tba
  rw [show N bab = 3 by norm_num [N,bab],show 3-1 = (2 : ℕ) by omega,
    catalan_two,hbab,mul_one] at tbab
  have iba : Linv ba = pure false 1 := by apply Five.ext <;> norm_num [Linv,ba,pure]
  have ibab : Linv bab = ba := by apply Five.ext <;> norm_num [Linv,bab,ba]
  have hp := pure_counts 1 (by omega)
  norm_num [catalan_zero] at hp
  have rba := entrance_recursion ba
  have rbab := entrance_recursion bab
  rw [iba,tba,hp.2.2.2,hp.2.2.1] at rba
  rw [ibab,tbab,rba] at rbab
  exact ⟨hba,tba,by omega,hbab,tbab,by omega⟩

private theorem word_tree_nonempty (g : Five) (w : WordFiber g) : Nonempty (TreeFiber g) := by
  obtain ⟨c,tail,he⟩ := List.exists_cons_of_ne_nil w.property.1
  exact ⟨⟨leftComb c tail, by
    rw [leftComb_word,← he]
    exact w.property.2⟩⟩

private theorem pure_nonempty (b : Bool) (n : ℕ) (hn : 0 < n) :
    Nonempty (TreeFiber (pure b n)) := by
  apply word_tree_nonempty (pure b n)
  exact ⟨List.replicate n b,by simpa using (Nat.ne_of_gt hn),pure_geometry b n⟩

private theorem actual_ratio (g : Five) (hg : Nonempty (TreeFiber g)) :
    0 < N g ∧ 0 < M g ∧ 1 ≤ (H g : ℝ)/M g ∧ (H g : ℝ)/M g ≤ B (N g) := by
  have hm : 0 < M g := Nat.card_pos_iff.mpr ⟨hg,inferInstance⟩
  have hp : 0 < (M g : ℝ) := by exact_mod_cast hm
  have hn : 0 < N g := by
    obtain ⟨t⟩ := hg
    rw [← tree_length g t]
    exact t.val.length_pos
  have est := uniform_actual_entrance_estimate g
  refine ⟨hn,hm,(le_div_iff₀ hp).mpr ?_,(div_le_iff₀ hp).mpr ?_⟩
  · simpa using (show (M g : ℝ) ≤ H g by exact_mod_cast est.1)
  · unfold B
    split_ifs with h2 h3
    · exact_mod_cast est.2.2.1 h2
    · have he : (2 : ℝ)*H g ≤ 5*M g := by exact_mod_cast est.2.2.2.1 h3
      linarith
    · by_cases h1 : N g = 1
      · exact_mod_cast est.2.1 h1
      · exact_mod_cast est.2.2.2.2.1 (by omega)

/-- Odd weights on a row list; reversing the descending rows gives the source prefix moment. -/
def prefixMoment : List ℕ → ℕ
  | [] => 0
  | a :: l => a + prefixMoment l + 2*l.sum

private theorem prefixMoment_cast (l : List ℕ) : (prefixMoment l : ℝ) = oddRows l := by
  induction l with
  | nil => simp [prefixMoment,oddRows]
  | cons a l ih => simp [prefixMoment,oddRows,ih]

private theorem oddRows_append (l : List ℕ) (a : ℕ) :
    oddRows (l++[a]) = oddRows l + (2*(l.length : ℝ)+1)*a := by
  induction l with
  | nil => simp [oddRows]
  | cons b l ih => simp [oddRows,ih,Nat.cast_add]; ring

private theorem oddRows_reverse (l : List ℕ) :
    oddRows l.reverse = 2*(l.length : ℝ)*l.sum - oddRows l := by
  induction l with
  | nil => simp [oddRows]
  | cons a l ih =>
    rw [List.reverse_cons,oddRows_append,ih]
    simp [oddRows,Nat.cast_add]
    ring

private theorem square_sum_cast (l : List ℕ) :
    (((l.map fun x => x^2).sum : ℕ) : ℝ) = squareRows l := by
  simp [squareRows,Function.comp_def]

/-- All arithmetic guards are supplied together by one actual word and its own prefix rows. -/
def SourceGuards (g : Five) : Prop :=
  ∃ w : WordFiber g, ∃ k q t : ℕ,
    k = (rows w.val).sum ∧ q = ((rows w.val).map fun x => x^2).sum ∧
    t = prefixMoment (rows w.val).reverse ∧
    k ≤ w.val.count true * w.val.count false ∧ 0 < N g ∧
    g.u = w.val.count true ∧ g.v = w.val.count false ∧
    (∃ d e f : ℤ, g.d = d ∧ g.e = e ∧ g.f = f) ∧
    (g.d+g.u*g.v)/2 = k ∧
    (g.e+6*g.u*k-g.u^2*g.v)/6 = q ∧
    (g.f+6*g.v*k+g.u*g.v^2)/6 = t

private theorem actual_guards (g : Five) (hg : Nonempty (TreeFiber g)) : SourceGuards g := by
  obtain ⟨s⟩ := hg
  let w : WordFiber g := ⟨wd s.val,wd_nonempty _,s.property⟩
  let u := w.val.count true
  let v := w.val.count false
  let k := (rows w.val).sum
  let q := ((rows w.val).map fun x => x^2).sum
  let t := prefixMoment (rows w.val).reverse
  have hk : k =
      D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge.scatteredTrueFalseCount w.val :=
    rows_sum w.val
  have hq : (q : ℝ) = squareRows (rows w.val) := square_sum_cast _
  have ht : (t : ℝ) = 2*(v : ℝ)*k - oddRows (rows w.val) := by
    rw [prefixMoment_cast,oddRows_reverse,rows_length]
  have hd := direct_list_fan w.val
  rw [w.property.2,← hk,← hq] at hd
  have he := endpoint w.val
  rw [w.property.2] at he
  have hd' : g.d = 2*(k : ℝ)-(u : ℝ)*v := congrArg Five.d hd
  have he' : g.e = (u : ℝ)^2*v-6*u*k+6*q := congrArg Five.e hd
  have hf' : g.f = 6*(t : ℝ)-6*v*k-(u : ℝ)*v^2 := by
    have hf := congrArg Five.f hd
    dsimp only at hf
    dsimp only [u,v]
    dsimp only [u,v] at ht
    linarith
  refine ⟨w,k,q,t,rfl,rfl,rfl,?_,?_,he.1,he.2,?_,?_,?_,?_⟩
  · rw [hk]; exact pair_count_bound _
  · rw [← tree_length g s]; exact s.val.length_pos
  · refine ⟨2*(k : ℤ)-(u : ℤ)*v,
      (u : ℤ)^2*v-6*u*k+6*q,6*(t : ℤ)-6*v*k-(u : ℤ)*v^2,?_,?_,?_⟩
    · push_cast; exact hd'
    · push_cast; exact he'
    · push_cast; exact hf'
  · rw [he.1,he.2,hd']; dsimp only [u,v]; ring
  · rw [he.1,he.2,he']; dsimp only [u,v]; ring
  · rw [he.1,he.2,hf']; dsimp only [u,v]; ring

/-- A whole-fiber maximizer, including both exceptional leaf counts. -/
def upper (n : ℕ) : Five := if n = 2 then ba else if n = 3 then bab else pure false n

private theorem upper_attainment (n : ℕ) (hn : 0 < n) :
    Nonempty (TreeFiber (upper n)) ∧ N (upper n) = n ∧
    (H (upper n) : ℝ)/M (upper n) = B n := by
  have hc := exceptional_counts
  unfold upper B
  split_ifs with h2 h3
  · subst n
    refine ⟨word_tree_nonempty ba ⟨[false,true],by simp,ba_geometry⟩,?_,?_⟩
    · norm_num [N,ba]
    · rw [hc.2.1,hc.2.2.1]; norm_num
  · subst n
    refine ⟨word_tree_nonempty bab ⟨[false,true,false],by simp,bab_geometry⟩,?_,?_⟩
    · norm_num [N,bab]
    · rw [hc.2.2.2.2.1,hc.2.2.2.2.2]; norm_num
  · have hp := pure_nonempty false n hn
    have hm : (M (pure false n) : ℝ) ≠ 0 := by
      exact_mod_cast (actual_ratio _ hp).2.1.ne'
    refine ⟨hp,pure_length false n,?_⟩
    rw [(pure_counts n hn).2.2.2,Nat.cast_mul,Nat.cast_ofNat]
    exact mul_div_cancel_right₀ 2 hm

private theorem pure_ratios (n : ℕ) (hn : 0 < n) :
    (H (pure true n) : ℝ)/M (pure true n) = 1 ∧
    (H (pure false n) : ℝ)/M (pure false n) = 2 := by
  have ht : (M (pure true n) : ℝ) ≠ 0 := by
    exact_mod_cast (actual_ratio _ (pure_nonempty true n hn)).2.1.ne'
  have hf : (M (pure false n) : ℝ) ≠ 0 := by
    exact_mod_cast (actual_ratio _ (pure_nonempty false n hn)).2.1.ne'
  constructor
  · rw [(pure_counts n hn).2.1]; exact div_self ht
  · rw [(pure_counts n hn).2.2.2,Nat.cast_mul,Nat.cast_ofNat]
    exact mul_div_cancel_right₀ 2 hf

/-- Complete sharp bounds and whole-fiber attainment for every nonempty native leaf count. -/
theorem sharp_geometry_entrance_ratio :
    (∀ g : Five, Nonempty (TreeFiber g) →
      SourceGuards g ∧ 0 < N g ∧ 0 < M g ∧
      1 ≤ (H g : ℝ)/M g ∧ (H g : ℝ)/M g ≤ B (N g) ∧
      M g ≤ H g ∧ H g ≤ 3*M g) ∧
    (∀ n : ℕ, 0 < n →
      Nonempty (TreeFiber (pure true n)) ∧ Nonempty (TreeFiber (pure false n)) ∧
      N (pure true n) = n ∧ N (pure false n) = n ∧
      m (pure true n) = 1 ∧ m (pure false n) = 1 ∧
      M (pure true n) = catalan (n-1) ∧ H (pure true n) = M (pure true n) ∧
      M (pure false n) = catalan (n-1) ∧ H (pure false n) = 2*M (pure false n) ∧
      (H (pure true n) : ℝ)/M (pure true n) = 1 ∧
      (H (pure false n) : ℝ)/M (pure false n) = 2 ∧
      Nonempty (TreeFiber (upper n)) ∧ N (upper n) = n ∧
      (H (upper n) : ℝ)/M (upper n) = B n) ∧
    (Nonempty (TreeFiber ba) ∧ N ba = 2 ∧
      (∀ w : WordFiber ba, w.val = [false,true]) ∧ m ba = 1 ∧ M ba = 1 ∧ H ba = 3 ∧
      Nonempty (TreeFiber bab) ∧ N bab = 3 ∧
      (∀ w : WordFiber bab, w.val = [false,true,false]) ∧ m bab = 1 ∧ M bab = 2 ∧ H bab = 5) ∧
    (∀ c : ℝ, (∀ g : Five, Nonempty (TreeFiber g) → (H g : ℝ)/M g ≤ c) → 3 ≤ c) := by
  have counts := exceptional_counts
  have hba : Nonempty (TreeFiber ba) :=
    word_tree_nonempty ba ⟨[false,true],by simp,ba_geometry⟩
  have hbab : Nonempty (TreeFiber bab) :=
    word_tree_nonempty bab ⟨[false,true,false],by simp,bab_geometry⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro g hg
    obtain ⟨hn,hm,hlo,hhi⟩ := actual_ratio g hg
    have he := uniform_actual_entrance_estimate g
    exact ⟨actual_guards g hg,hn,hm,hlo,hhi,he.1,he.2.2.2.2.2⟩
  · intro n hn
    obtain ⟨mt,ht,mf,hf⟩ := pure_counts n hn
    obtain ⟨rt,rf⟩ := pure_ratios n hn
    exact ⟨pure_nonempty true n hn,pure_nonempty false n hn,
      pure_length true n,pure_length false n,pure_word_card true n hn,
      pure_word_card false n hn,mt,ht,mf,hf,rt,rf,upper_attainment n hn⟩
  · exact ⟨hba,by norm_num [N,ba],ba_unique,counts.1,counts.2.1,counts.2.2.1,
      hbab,by norm_num [N,bab],bab_unique,counts.2.2.2.1,counts.2.2.2.2.1,counts.2.2.2.2.2⟩
  · intro c hc
    have he := hc ba hba
    rw [counts.2.1,counts.2.2.1] at he
    norm_num at he
    exact he

#check actual_fiber_counting
#check uniform_actual_entrance_estimate
#check sharp_geometry_entrance_ratio
#print axioms actual_fiber_counting
#print axioms uniform_actual_entrance_estimate
#print axioms sharp_geometry_entrance_ratio


end D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio
