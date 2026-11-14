/- GID: D5/S3/Analytic/Spectral/FillmanLimGapRichWords
   generality: G
   mirror-B: D5/B/S3/Analytic/Spectral/FillmanLimGapRichWords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Periodic word metrics and positive products admit compatible realizations. -/

/-
admission_basis: escape-witness
escape_witness: closureWordRealization
Four-slot escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30475
Direct frozen dependencies (declaration identities):
none
Per-declaration classification; definitions specify objects rather than theorem assertions.
Consumed bind-only helpers organize proofs and supply no independent escape witness.
Word: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: GapRichWithExceptionalSet,Good,WordOver,closureWordRealization,concat,extend,extend_concat,gap_rich_components,goodDistance,goodOfForallTwo,goodSelf,good_concat,not_gap_rich_of_obstructions,pairWord,periodicLetter,periodic_letter_mod,product_not_gap_rich,singleWord,single_word_close,sum_not_gap_rich,union_not_gap_rich,union_word_bound,wordDistance,wordDistanceLtIff,wordOfList,word_over_concat
concat: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: closureWordRealization,extend_concat,good_concat,word_over_concat
periodicLetter: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: Good,goodDistance,goodOfForallTwo,goodSelf,good_concat,pair_word_periodic,periodic_letter_mod,single_word_close,union_word_bound,wordDistance,wordDistanceLtIff
wordDistance: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: GapRichWithExceptionalSet,gap_rich_components,goodDistance,not_gap_rich_of_obstructions,product_not_gap_rich,single_word_close,sum_not_gap_rich,union_not_gap_rich,union_word_bound,wordDistanceLtIff
extend: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: GapRichWithExceptionalSet,closureWordRealization,extend_concat,gap_rich_components,not_gap_rich_of_obstructions,product_not_gap_rich,sum_not_gap_rich,union_not_gap_rich,union_word_bound
transfer: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: blockTransfer,block_transfer_append,block_transfer_determinant,cancellation_resonance,j_square,l_gap_rich,l_relative_trace,l_transfer_resonance,neg_j_trace_bound,sum_near_resonance,sum_not_gap_rich,sum_transfer_resonance,transfer_det,u_gap_rich,u_relative_trace,u_transfer_resonance,union_near_u_resonance,union_near_v_resonance,union_word_bound,v_gap_rich,v_relative_trace,v_transfer_resonance
blockTransfer: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: GapRichWithExceptionalSet,block_transfer_append,block_transfer_determinant,cancellation_resonance,gap_rich_components,l_relative_trace,l_transfer_resonance,not_gap_rich_of_obstructions,product_near_resonance,product_not_gap_rich,sum_near_resonance,sum_not_gap_rich,sum_transfer_resonance,u_relative_trace,u_transfer_resonance,union_near_u_resonance,union_near_v_resonance,union_not_gap_rich,union_word_bound,v_relative_trace,v_transfer_resonance
WordOver: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: GapRichWithExceptionalSet,closureWordRealization,gap_rich_components,not_gap_rich_of_obstructions,product_not_gap_rich,sum_not_gap_rich,union_not_gap_rich,union_word_bound,word_over_concat
GapRichWithExceptionalSet: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: GapRich,gap_rich_components,l_gap_rich,not_gap_rich_of_obstructions,u_gap_rich,v_gap_rich
GapRich: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: claim,l_gap_rich,not_gap_rich_of_obstructions,product_not_gap_rich,result,sum_not_gap_rich,u_gap_rich,union_not_gap_rich,v_gap_rich
cartesianProduct: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: claim,product_center_member,product_near_resonance,product_not_gap_rich,result
periodic_letter_mod: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: goodDistance,wordDistanceLtIff
wordDistanceLtIff: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: goodDistance,single_word_close,union_word_bound
Good: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: closureWordRealization,gap_rich_components,goodDistance,goodOfForallTwo,goodSelf,good_concat
goodSelf: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: gap_rich_components
goodDistance: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: gap_rich_components
good_concat: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: closureWordRealization
word_over_concat: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: closureWordRealization
foldLeftStart: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: block_transfer_append,extend_concat,fold_constant,gap_rich_components,pairs_fold
extend_concat: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: closureWordRealization
wordOfList: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: gap_rich_components,wordOfListLetters
wordOfListLetters: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: gap_rich_components
goodOfForallTwo: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: gap_rich_components
closureWordRealization: proof_shape: content; escape_witness: closureWordRealization; Direct frozen dependencies: none; consumers: gap_rich_components
utility: none; the payload uses infinite alphabets, arbitrary positive word lengths,
and an unrestricted positive-semigroup criterion, rather than a finite checker.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

namespace D5.S3.Analytic.Spectral.FillmanLimGapRichWords

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
open Set
open scoped Topology Pointwise

structure Word (Y : Type) where
  length : ℕ+
  letter : Fin (length : ℕ) → Y

/-- Concatenation in the displayed coordinate order. -/
def concat {Y : Type} (x y : Word Y) : Word Y :=
  ⟨x.length + y.length, Fin.append x.letter y.letter⟩

/-- The j-th letter of the infinite periodic repetition, indexed from zero. -/
def periodicLetter {Y : Type} (x : Word Y) (j : ℕ) : Y :=
  x.letter ⟨j % (x.length : ℕ), Nat.mod_lt _ x.length.pos⟩

/-- The finite supremum over exactly length(x) * length(y) positions. -/
def wordDistance {Y : Type} [MetricSpace Y] (x y : Word Y) : ℝ :=
  (Finset.range ((x.length : ℕ) * (y.length : ℕ))).sup'
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt (Nat.mul_pos x.length.pos y.length.pos)))
    (fun j => dist (periodicLetter x j) (periodicLetter y j))

/-- A(y sharp z,E) = A(z,E) A(y,E), including the source's reversed order. -/
def extend {Y : Type} (A : Y → ℝ → (Matrix (Fin 2) (Fin 2) ℝ)) (x : Word Y) (E : ℝ) : (Matrix (Fin 2) (Fin 2) ℝ) :=
  (List.ofFn x.letter).foldl (fun M y => A y E * M) 1

/-- Definition 2.9: the scalar Schrödinger transfer matrix. -/
def transfer (x E : ℝ) : (Matrix (Fin 2) (Fin 2) ℝ) :=
  !![E - x, -1; 1, 0]

/-- A length-k potential block is itself a scalar word, in coordinate order. -/
def blockTransfer {k : ℕ} (x : (EuclideanSpace ℝ (Fin k))) (E : ℝ) : (Matrix (Fin 2) (Fin 2) ℝ) :=
  (List.ofFn (fun i : Fin k => x i)).foldl (fun M a => transfer a E * M) 1

/-- Membership of every letter of a nonempty word in the alphabet. -/
def WordOver {Y : Type} (X : Set Y) (x : Word Y) : Prop :=
  ∀ i : Fin (x.length : ℕ), x.letter i ∈ X

/-- Definition 2.7 for the fixed continuous polynomial transfer map.
All energies outside the discrete set, all words, all positive tolerances,
and perturbing words of every possible positive length are included. -/
def GapRichWithExceptionalSet {k : ℕ} (X : Set ((EuclideanSpace ℝ (Fin k)))) (S : Set ℝ) : Prop :=
  IsDiscrete S ∧
    ∀ E : ℝ, E ∉ S →
      ∀ x : Word ((EuclideanSpace ℝ (Fin k))), WordOver X x →
        ∀ ε : ℝ, 0 < ε →
          ∃ y : Word ((EuclideanSpace ℝ (Fin k))), WordOver X y ∧ wordDistance x y < ε ∧
            2 < |Matrix.trace (extend blockTransfer y E)|

/-- The source permits an arbitrary discrete exceptional set. -/
def GapRich {k : ℕ} (X : Set ((EuclideanSpace ℝ (Fin k)))) : Prop :=
  ∃ S : Set ℝ, GapRichWithExceptionalSet X S

/-- Cartesian product as an ordered block in R^(k+ell), not a product alphabet. -/
def cartesianProduct {k ℓ : ℕ} (X₁ : Set ((EuclideanSpace ℝ (Fin k)))) (X₃ : Set ((EuclideanSpace ℝ (Fin ℓ)))) :
    Set ((EuclideanSpace ℝ (Fin (k + ℓ)))) :=
  {z | ∃ x : (EuclideanSpace ℝ (Fin k)), x ∈ X₁ ∧ ∃ y : (EuclideanSpace ℝ (Fin ℓ)), y ∈ X₃ ∧
    z = WithLp.toLp 2 (Fin.append (WithLp.ofLp x) (WithLp.ofLp y))}

private theorem periodic_letter_mod {Y : Type} (x : Word Y) (N j : ℕ)
    (hN : (x.length : ℕ) ∣ N) : periodicLetter x (j % N) = periodicLetter x j := by
  unfold periodicLetter
  congr 1
  apply Fin.ext
  exact Nat.mod_mod_of_dvd j hN

theorem wordDistanceLtIff {Y : Type} [MetricSpace Y]
    (x y : Word Y) (ε : ℝ) :
    wordDistance x y < ε ↔ ∀ j : ℕ,
      dist (periodicLetter x j) (periodicLetter y j) < ε := by
  unfold wordDistance
  rw [Finset.sup'_lt_iff]
  constructor
  · intro h j
    have hp : 0 < (x.length : ℕ)*(y.length : ℕ) := Nat.mul_pos x.length.pos y.length.pos
    have hj := h (j % ((x.length : ℕ)*(y.length : ℕ)))
      (Finset.mem_range.mpr (Nat.mod_lt j hp))
    rwa [periodic_letter_mod x _ _ (dvd_mul_right _ _),
      periodic_letter_mod y _ _ (dvd_mul_left _ _)] at hj
  · intro h j hj
    exact h j

def Good {Y : Type} [MetricSpace Y] (x : Word Y) (ε : ℝ) (y : Word Y) : Prop :=
  (x.length : ℕ) ∣ (y.length : ℕ) ∧
    ∀ i : Fin (y.length : ℕ), dist (periodicLetter x i) (y.letter i) < ε

theorem goodSelf {Y : Type} [MetricSpace Y] (x : Word Y)
    (ε : ℝ) (hε : 0 < ε) : Good x ε x := by
  refine ⟨dvd_refl _, fun i => ?_⟩
  simpa [periodicLetter, Nat.mod_eq_of_lt i.isLt] using hε

theorem goodDistance {Y : Type} [MetricSpace Y] (x y : Word Y)
    (ε : ℝ) (h : Good x ε y) : wordDistance x y < ε := by
  apply (wordDistanceLtIff x y ε).mpr
  intro j
  have hh := h.2 (⟨j % (y.length : ℕ), Nat.mod_lt j y.length.pos⟩)
  change dist (periodicLetter x (j % (y.length : ℕ))) (periodicLetter y j) < ε at hh
  rwa [periodic_letter_mod x _ _ h.1] at hh

private theorem good_concat {Y : Type} [MetricSpace Y] (x y z : Word Y)
    (ε : ℝ) (hy : Good x ε y) (hz : Good x ε z) : Good x ε (concat y z) := by
  refine ⟨dvd_add hy.1 hz.1, ?_⟩
  change ∀ i : Fin ((y.length : ℕ)+(z.length : ℕ)),
    dist (periodicLetter x i) (Fin.append y.letter z.letter i) < ε
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa using hy.2 j
  · have hperiod : periodicLetter x ((y.length : ℕ)+(j : ℕ)) = periodicLetter x j := by
      unfold periodicLetter
      congr 1
      apply Fin.ext
      simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hy.1]
    simpa only [Fin.val_natAdd, Fin.append_right, hperiod] using hz.2 j

private theorem word_over_concat {Y : Type} (X : Set Y) (x y : Word Y)
    (hx : WordOver X x) (hy : WordOver X y) : WordOver X (concat x y) := by
  change ∀ i : Fin ((x.length : ℕ)+(y.length : ℕ)),
    Fin.append x.letter y.letter i ∈ X
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    exact hx j
  · rw [Fin.append_right]
    exact hy j

theorem foldLeftStart {Y : Type} (f : Y → (Matrix (Fin 2) (Fin 2) ℝ)) (l : List Y) (M : (Matrix (Fin 2) (Fin 2) ℝ)) :
    l.foldl (fun B a => f a * B) M = l.foldl (fun B a => f a * B) 1 * M := by
  simpa only [one_mul] using (List.foldl_hom (fun B => B * M)
    (g₁ := fun B a => f a * B) (g₂ := fun B a => f a * B)
    (l := l) (init := 1) (fun B a => (mul_assoc (f a) B M).symm))

private theorem extend_concat {Y : Type} (A : Y → ℝ → (Matrix (Fin 2) (Fin 2) ℝ))
    (x y : Word Y) (E : ℝ) : extend A (concat x y) E = extend A y E * extend A x E := by
  change (List.ofFn (Fin.append x.letter y.letter)).foldl _ 1 = _
  rw [List.ofFn_fin_append, List.foldl_append]
  exact foldLeftStart _ _ _

def wordOfList {Y : Type} (l : List Y) (hl : 0 < l.length) : Word Y :=
  ⟨⟨l.length,hl⟩,fun i => l.get i⟩

theorem wordOfListLetters {Y : Type} (l : List Y) (hl : 0 < l.length) :
    List.ofFn (wordOfList l hl).letter = l := by
  simp [wordOfList]

theorem goodOfForallTwo {Y : Type} [MetricSpace Y] (x y : Word Y) (ε : ℝ)
    (h : List.Forall₂ (fun a b => dist a b < ε)
      (List.ofFn x.letter) (List.ofFn y.letter)) : Good x ε y := by
  have hn : (x.length : ℕ) = (y.length : ℕ) := by simpa using h.length_eq
  refine ⟨hn ▸ dvd_refl _, fun i => ?_⟩
  have hh := h.get (i := i.val) (by simpa [hn] using i.isLt) (by simpa using i.isLt)
  have hi : periodicLetter x i = x.letter ⟨i,by simpa [hn] using i.isLt⟩ := by
    unfold periodicLetter
    congr 1
    apply Fin.ext
    exact Nat.mod_eq_of_lt (by simpa [hn] using i.isLt)
  simpa [List.get_ofFn,hi] using hh

theorem closureWordRealization {Y : Type} [MetricSpace Y]
    (X : Set Y) (A : Y → ℝ → (Matrix (Fin 2) (Fin 2) ℝ)) (x y : Word Y) (E ε : ℝ)
    (hx : Good x ε x) (hy : Good x ε y)
    (hxX : WordOver X x) (hyX : WordOver X y)
    (C : (Matrix (Fin 2) (Fin 2) ℝ)) (hC : C ∈ Submonoid.closure ({extend A x E,extend A y E} : Set (Matrix (Fin 2) (Fin 2) ℝ))) :
    C = 1 ∨ ∃ z : Word Y, WordOver X z ∧ Good x ε z ∧ extend A z E = C := by
  induction hC using Submonoid.closure_induction with
  | mem C hC =>
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hC
    rcases hC with rfl | rfl
    · exact Or.inr ⟨x,hxX,hx,rfl⟩
    · exact Or.inr ⟨y,hyX,hy,rfl⟩
  | one => exact Or.inl rfl
  | mul C D hC hD ihC ihD =>
    rcases ihC with rfl | ⟨u,huX,hu,hU⟩
    · simpa using ihD
    rcases ihD with rfl | ⟨v,hvX,hv,hV⟩
    · simpa using (Or.inr ⟨u,huX,hu,hU⟩ :
        C=1 ∨ ∃ z : Word Y, WordOver X z ∧ Good x ε z ∧ extend A z E=C)
    · refine Or.inr ⟨concat v u,word_over_concat X v u hvX huX,
        good_concat x v u ε hv hu,?_⟩
      rw [extend_concat,hU,hV]

end
end D5.S3.Analytic.Spectral.FillmanLimGapRichWords
