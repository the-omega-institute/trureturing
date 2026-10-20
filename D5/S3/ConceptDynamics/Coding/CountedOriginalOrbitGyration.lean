/- GID: D5/S3/ConceptDynamics/Coding/CountedOriginalOrbitGyration
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedOriginalOrbitGyration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original counted orbits, order types, and integral polynomial lifts. -/

import D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
import Mathlib.Order.PiLex
import Mathlib.Data.Finset.Max
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Classical

namespace D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration

open scoped BigOperators
open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.FixedBlockRigidity.BlockCoordinates

/-! Actual numbered edges: equality and finiteness, with no inhabitedness premise. -/

theorem edge_eq_coordinates {n m : ℕ} {M : CountMat n m} {a b : Edge M}
    (hs : a.source = b.source) (ht : a.target = b.target)
    (hn : a.number.val = b.number.val) : a = b := by
  rcases a with ⟨i,j,a⟩
  rcases b with ⟨i',j',b⟩
  dsimp at hs ht hn
  subst i'
  subst j'
  have hab : a = b := Fin.ext hn
  subst b
  rfl

private def edgeSigmaEquiv {n m : ℕ} (M : CountMat n m) :
    Edge M ≃ (Σ i : Fin n, Σ j : Fin m, Fin (M i j)) where
  toFun a := ⟨a.source,a.target,a.number⟩
  invFun a := ⟨a.1,a.2.1,a.2.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by rcases a with ⟨i,j,k⟩; rfl

instance originalEdgeFintype {n m : ℕ} (M : CountMat n m) : Fintype (Edge M) :=
  Fintype.ofEquiv _ (edgeSigmaEquiv M).symm

/-- All legal cyclic words on the ORIGINAL numbered graph. -/
abbrev LegalWord {n : ℕ} (A : CountMat n n) (d : ℕ) [NeZero d] :=
  {a : Fin d → Edge A // ∀ t, (a t).target = (a (t+1)).source}

def numberedWord {n m d : ℕ} [NeZero d] (z : Entry n m → ℕ)
    (p : Σ w : VertexWord n m d, Labels w z) :
    LegalWord (rMatrix z * sMatrix z) d :=
  ⟨sourceEdge p.1 z p.2, sourceEdge_legal p.1 z p.2⟩

/-- Split every original edge. Its first outside endpoint and actual middle
vertex recover the two vertex words. The outside seam is supplied by legality. -/
def recoverVertices {n m d : ℕ} [NeZero d] (z : Entry n m → ℕ)
    (a : LegalWord (rMatrix z * sMatrix z) d) : VertexWord n m d :=
  (fun t => (a.val t).source,
   fun t => (split (rMatrix z) (sMatrix z) (a.val t)).1.target)

/-- The values are the two canonical split numbers, not newly assigned ranks.
Subtype proofs implement the dependent occurrence and seam casts. -/
def recoverLabels {n m d : ℕ} [NeZero d] (z : Entry n m → ℕ)
    (a : LegalWord (rMatrix z * sMatrix z) d) : Labels (recoverVertices z a) z := by
  intro e q
  cases e with
  | inl ij =>
    rcases q with ⟨t, ht⟩
    cases ht
    refine ⟨(split (rMatrix z) (sMatrix z) (a.val t)).1.number.val, ?_⟩
    exact (split (rMatrix z) (sMatrix z) (a.val t)).1.number.isLt
  | inr ji =>
    rcases q with ⟨t, ht⟩
    cases ht
    refine ⟨(split (rMatrix z) (sMatrix z) (a.val t)).2.number.val, ?_⟩
    change (split (rMatrix z) (sMatrix z) (a.val t)).2.number.val <
      (sMatrix z) ((recoverVertices z a).2 t) ((a.val (t+1)).source)
    rw [← a.property t]
    exact (split (rMatrix z) (sMatrix z) (a.val t)).2.number.isLt

def recoverNumberedWord {n m d : ℕ} [NeZero d] (z : Entry n m → ℕ)
    (a : LegalWord (rMatrix z * sMatrix z) d) :
    Σ w : VertexWord n m d, Labels w z :=
  ⟨recoverVertices z a, recoverLabels z a⟩

theorem numberedWord_recover {n m d : ℕ} [NeZero d] (z : Entry n m → ℕ)
    (a : LegalWord (rMatrix z * sMatrix z) d) :
    numberedWord z (recoverNumberedWord z a) = a := by
  apply Subtype.ext
  funext t
  let w := recoverVertices z a
  let l := recoverLabels z a
  let r : Edge (rMatrix z) :=
    ⟨w.1 t,w.2 t,l (Sum.inl (w.1 t,w.2 t)) ⟨t,rfl⟩⟩
  let s : Edge (sMatrix z) :=
    ⟨w.2 t,w.1 (t+1),l (Sum.inr (w.2 t,w.1 (t+1))) ⟨t,rfl⟩⟩
  have hr : r = (split (rMatrix z) (sMatrix z) (a.val t)).1 :=
    edge_eq_coordinates (split_source (rMatrix z) (sMatrix z) (a.val t)).symm rfl rfl
  have hs : s = (split (rMatrix z) (sMatrix z) (a.val t)).2 :=
    edge_eq_coordinates (split_middle (rMatrix z) (sMatrix z) (a.val t))
      ((a.property t).symm.trans (split_target (rMatrix z) (sMatrix z) (a.val t)).symm) rfl
  change join (rMatrix z) (sMatrix z) r s rfl = a.val t
  simp only [hr, hs, join_split]

theorem numberedWord_injective {n m d : ℕ} [NeZero d] (z : Entry n m → ℕ) :
    Function.Injective (numberedWord (d := d) z) := by
  rintro ⟨⟨i,j⟩,l⟩ ⟨⟨i',j'⟩,l'⟩ h
  have he : ∀ t, sourceEdge (i,j) z l t = sourceEdge (i',j') z l' t :=
    fun t => congrFun (congrArg Subtype.val h) t
  have hi : i = i' := funext fun t => congrArg Edge.source (he t)
  have hj : j = j' := by
    funext t
    have hs := congrArg (fun a => (split (rMatrix z) (sMatrix z) a).1.target) (he t)
    simpa only [sourceEdge, split_join] using hs
  subst i'
  subst j'
  have hl : l = l' := by
    funext e q
    cases e with
    | inl ij =>
      rcases q with ⟨t,ht⟩
      cases ht
      apply Fin.ext
      have hs := congrArg (split (rMatrix z) (sMatrix z)) (he t)
      dsimp only [sourceEdge] at hs
      rw [split_join, split_join] at hs
      exact congrArg (fun p => p.1.number.val) hs
    | inr ji =>
      rcases q with ⟨t,ht⟩
      cases ht
      apply Fin.ext
      have hs := congrArg (split (rMatrix z) (sMatrix z)) (he t)
      dsimp only [sourceEdge] at hs
      rw [split_join, split_join] at hs
      exact congrArg (fun p => p.2.number.val) hs
  subst l'
  rfl

/-- The dependent inverse includes ALL legal original-edge words, even when
some entries vanish. No graph-inhabited or realization premise occurs. -/
def numberedWordEquiv {n m d : ℕ} [NeZero d] (z : Entry n m → ℕ) :
    (Σ w : VertexWord n m d, Labels w z) ≃
      LegalWord (rMatrix z * sMatrix z) d where
  toFun := numberedWord z
  invFun := recoverNumberedWord z
  left_inv p := numberedWord_injective z (numberedWord_recover z (numberedWord z p))
  right_inv := numberedWord_recover z

/-! Restriction/extension on the actual signed-time Path carrier. -/

abbrev PeriodicPath {n : ℕ} (A : CountMat n n) (d : ℕ) :=
  {x : Path A // Function.IsPeriodicPt (shift A) d x}

theorem path_period_coordinate {n d : ℕ} {A : CountMat n n}
    (x : Path A) (hx : Function.IsPeriodicPt (shift A) d x) (t : ℤ) :
    x.val (t+(d : ℤ)) = x.val t := by
  have h : (shift A)^[d] x = x := hx
  rw [show (shift A)^[d] x = translate (countedGraph A) (d : ℤ) x from
    shift_iterate_translate (countedGraph A) d x] at h
  exact congrArg (fun y : Path A => y.val t) h

theorem path_period_coordinate_nat_mul {n d : ℕ} {A : CountMat n n}
    (x : Path A) (hx : Function.IsPeriodicPt (shift A) d x) :
    ∀ q : ℕ, ∀ t : ℤ, x.val (t+(q : ℤ)*(d : ℤ)) = x.val t := by
  intro q
  induction q with
  | zero => intro t; simp
  | succ q ih =>
    intro t
    calc
      x.val (t+((q+1 : ℕ) : ℤ)*(d : ℤ)) =
          x.val ((t+(q : ℤ)*(d : ℤ))+(d : ℤ)) := by congr 1; push_cast; ring
      _ = x.val (t+(q : ℤ)*(d : ℤ)) := path_period_coordinate x hx _
      _ = x.val t := ih t

theorem path_period_coordinate_int_mul {n d : ℕ} {A : CountMat n n}
    (x : Path A) (hx : Function.IsPeriodicPt (shift A) d x) (q t : ℤ) :
    x.val (t+q*(d : ℤ)) = x.val t := by
  cases q with
  | ofNat q => exact path_period_coordinate_nat_mul x hx q t
  | negSucc q =>
    have h := path_period_coordinate_nat_mul x hx (q+1)
      (t-((q+1 : ℕ) : ℤ)*(d : ℤ))
    have he : (t-((q+1 : ℕ) : ℤ)*(d : ℤ))+
        ((q+1 : ℕ) : ℤ)*(d : ℤ) = t := by ring
    rw [he] at h
    simpa only [Int.negSucc_eq, Int.natCast_add, Int.natCast_one,
      neg_mul, sub_eq_add_neg] using h.symm

/-- Euclidean blockAddress, including negative quotients, supplies the exact
coordinate reduction. It is not a specialization of expanded-group histories. -/
theorem path_at_timeIndex {n d : ℕ} [NeZero d] {A : CountMat n n}
    (x : Path A) (hx : Function.IsPeriodicPt (shift A) d x) (t : ℤ) :
    x.val ((timeIndex (d := d) t).val : ℤ) = x.val t := by
  let q := (blockAddress (Nat.pos_of_ne_zero (NeZero.ne d)) t).1
  have ha := assemble_address (Nat.pos_of_ne_zero (NeZero.ne d)) t
  have he : ((timeIndex (d := d) t).val : ℤ)+q*(d : ℤ) = t := by
    change q*(d : ℤ)+(timeIndex (d := d) t).val = t at ha
    simpa only [add_comm] using ha
  have h := path_period_coordinate_int_mul x hx q ((timeIndex (d := d) t).val : ℤ)
  rw [he] at h
  exact h.symm

def restrictWord {n d : ℕ} [NeZero d] {A : CountMat n n}
    (x : Path A) (hx : Function.IsPeriodicPt (shift A) d x) : LegalWord A d :=
  ⟨fun t => x.val (t.val : ℤ), by
    intro t
    have h := path_at_timeIndex x hx ((t.val : ℤ)+1)
    rw [timeIndex_succ, timeIndex_nat] at h
    exact (x.property (t.val : ℤ)).trans (congrArg Edge.source h.symm)⟩

theorem cyclicPath_restrict {n d : ℕ} [NeZero d] {A : CountMat n n}
    (x : Path A) (hx : Function.IsPeriodicPt (shift A) d x) :
    cyclicPath (restrictWord x hx).val (restrictWord x hx).property = x := by
  apply Subtype.ext
  funext t
  exact path_at_timeIndex x hx t

theorem restrict_cyclicPath {n d : ℕ} [NeZero d] {A : CountMat n n}
    (a : LegalWord A d) :
    restrictWord (cyclicPath a.val a.property) (cyclicPath_period a.val a.property) = a := by
  apply Subtype.ext
  funext t
  exact cyclicPath_at a.val a.property t

def periodicWordEquiv {n d : ℕ} [NeZero d] (A : CountMat n n) :
    LegalWord A d ≃ PeriodicPath A d where
  toFun a := ⟨cyclicPath a.val a.property, cyclicPath_period a.val a.property⟩
  invFun x := restrictWord x.val x.property
  left_inv := restrict_cyclicPath
  right_inv x := Subtype.ext (cyclicPath_restrict x.val x.property)

/-! Lex order uses Mathlib's ordered finite Pi carrier and the original edge
key (source,target,number). These keys are solely order embeddings. -/

private def originalEdgeKey {n : ℕ} {A : CountMat n n} (a : Edge A) :
    Lex (Fin n × Lex (Fin n × ℕ)) :=
  toLex (a.source,toLex (a.target,a.number.val))

private theorem originalEdgeKey_injective {n : ℕ} {A : CountMat n n} :
    Function.Injective (@originalEdgeKey n A) := by
  intro a b h
  have hs := congrArg (fun p : Lex (Fin n × Lex (Fin n × ℕ)) => (ofLex p).1) h
  have ht := congrArg (fun p : Lex (Fin n × Lex (Fin n × ℕ)) =>
    (ofLex (ofLex p).2).1) h
  have hn := congrArg (fun p : Lex (Fin n × Lex (Fin n × ℕ)) =>
    (ofLex (ofLex p).2).2) h
  exact edge_eq_coordinates hs ht hn

private theorem originalEdgeKey_lt_iff {n : ℕ} {A : CountMat n n} (a b : Edge A) :
    originalEdgeKey a < originalEdgeKey b ↔ EdgeLT a b := by
  simp only [originalEdgeKey, Prod.Lex.toLex_lt_toLex, EdgeLT]

def originalWordKey {n d : ℕ} {A : CountMat n n} (a : Fin d → Edge A) :
    Lex (Fin d → Lex (Fin n × Lex (Fin n × ℕ))) :=
  toLex (fun t => originalEdgeKey (a t))

theorem originalWordKey_injective {n d : ℕ} {A : CountMat n n} :
    Function.Injective (@originalWordKey n d A) := by
  intro a b h
  funext t
  exact originalEdgeKey_injective (congrFun h t)

theorem originalWordKey_lt_iff {n d : ℕ} {A : CountMat n n} (a b : Fin d → Edge A) :
    originalWordKey a < originalWordKey b ↔ WordLT a b := by
  change (∃ t : Fin d, (∀ u : Fin d, u < t →
    originalEdgeKey (a u) = originalEdgeKey (b u)) ∧
      originalEdgeKey (a t) < originalEdgeKey (b t)) ↔ _
  simp only [originalEdgeKey_injective.eq_iff, originalEdgeKey_lt_iff, WordLT]

theorem wordLT_irrefl {n d : ℕ} {A : CountMat n n} (a : Fin d → Edge A) :
    ¬ WordLT a a := by
  rw [← originalWordKey_lt_iff]
  exact lt_irrefl _

theorem wordLT_trans {n d : ℕ} {A : CountMat n n} {a b c : Fin d → Edge A}
    (hab : WordLT a b) (hbc : WordLT b c) : WordLT a c := by
  rw [← originalWordKey_lt_iff] at hab hbc ⊢
  exact lt_trans hab hbc

theorem wordLT_asymm {n d : ℕ} {A : CountMat n n} {a b : Fin d → Edge A}
    (hab : WordLT a b) : ¬ WordLT b a :=
  fun hba => wordLT_irrefl a (wordLT_trans hab hba)

@[simp] theorem rotate_zero {d : ℕ} [NeZero d] {α : Type*} (a : Fin d → α) :
    rotate 0 a = a := by funext t; simp [rotate]

theorem rotate_rotate {d : ℕ} [NeZero d] {α : Type*} (i j : Fin d) (a : Fin d → α) :
    rotate i (rotate j a) = rotate (i+j) a := by
  funext t
  simp only [rotate, add_assoc]

theorem primitive_rotation_injective {d : ℕ} [NeZero d] {α : Type*}
    {a : Fin d → α} (ha : Primitive a) : Function.Injective (fun k => rotate k a) := by
  intro i j h
  by_contra hij
  have hs : i-j ≠ 0 := sub_ne_zero.mpr hij
  apply ha (i-j) hs
  have h' := congrArg (rotate (-j)) h
  simpa only [rotate_rotate, neg_add_cancel, rotate_zero, sub_eq_add_neg,
    add_comm (-j) i] using h'

theorem strictLeast_rotate_index_zero {n d : ℕ} [NeZero d] {A : CountMat n n}
    {a : Fin d → Edge A} (ha : StrictLeast a) {k : Fin d}
    (hk : StrictLeast (rotate k a)) : k = 0 := by
  by_contra hne
  have h₁ := ha k hne
  have h₂ := hk (-k) (neg_ne_zero.mpr hne)
  rw [rotate_negative] at h₂
  exact wordLT_asymm h₁ h₂

/-- Finite minimum of actual numbered-word keys. Primitivity makes EVERY
nonzero comparison strict; it is not an assumed representative selector. -/
theorem exists_strictLeast_rotation {n d : ℕ} [NeZero d] {A : CountMat n n}
    (a : Fin d → Edge A) (ha : Primitive a) : ∃ k : Fin d, StrictLeast (rotate k a) := by
  classical
  let s := Finset.univ.image (fun k : Fin d => originalWordKey (rotate k a))
  have hs : s.Nonempty := ⟨originalWordKey (rotate 0 a),
    Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩⟩
  obtain ⟨k,_,hk⟩ := Finset.mem_image.mp (s.min'_mem hs)
  refine ⟨k, ?_⟩
  intro l hl
  have hle : originalWordKey (rotate k a) ≤ originalWordKey (rotate (l+k) a) := by
    rw [hk]
    exact s.min'_le _ (Finset.mem_image.mpr ⟨l+k,Finset.mem_univ _,rfl⟩)
  have hne : originalWordKey (rotate k a) ≠ originalWordKey (rotate (l+k) a) := by
    intro he
    have hi := primitive_rotation_injective ha (originalWordKey_injective he)
    have hi' : 0+k = l+k := by simpa only [zero_add] using hi
    exact hl (add_right_cancel hi').symm
  have hlt := lt_of_le_of_ne hle hne
  rw [← originalWordKey_lt_iff, rotate_rotate]
  exact hlt

theorem existsUnique_strictLeast_rotation {n d : ℕ} [NeZero d] {A : CountMat n n}
    (a : Fin d → Edge A) (ha : Primitive a) : ∃! k : Fin d, StrictLeast (rotate k a) := by
  obtain ⟨k,hk⟩ := exists_strictLeast_rotation a ha
  refine ⟨k,hk,?_⟩
  intro l hl
  have h : StrictLeast (rotate (l-k) (rotate k a)) := by
    simpa only [rotate_rotate, sub_add_cancel] using hl
  exact sub_eq_zero.mp (strictLeast_rotate_index_zero hk h)

def leastIndex {n d : ℕ} [NeZero d] {A : CountMat n n}
    (a : Fin d → Edge A) (ha : Primitive a) : Fin d :=
  Classical.choose (existsUnique_strictLeast_rotation a ha)

theorem leastIndex_spec {n d : ℕ} [NeZero d] {A : CountMat n n}
    (a : Fin d → Edge A) (ha : Primitive a) :
    StrictLeast (rotate (leastIndex a ha) a) :=
  (Classical.choose_spec (existsUnique_strictLeast_rotation a ha)).1

theorem leastIndex_unique {n d : ℕ} [NeZero d] {A : CountMat n n}
    (a : Fin d → Edge A) (ha : Primitive a) (k : Fin d)
    (hk : StrictLeast (rotate k a)) : k = leastIndex a ha :=
  (Classical.choose_spec (existsUnique_strictLeast_rotation a ha)).2 k hk

/-! Primitive actual paths, their orbit relation, and their proved canonical basis. -/

abbrev PrimitivePath {n : ℕ} (A : CountMat n n) (d : ℕ) :=
  {x : Path A // Function.minimalPeriod (shift A) x = d}

theorem primitivePath_period {n d : ℕ} {A : CountMat n n} (x : PrimitivePath A d) :
    Function.IsPeriodicPt (shift A) d x.val := by
  simpa only [x.property] using Function.isPeriodicPt_minimalPeriod (shift A) x.val

def primitiveRestriction {n d : ℕ} [NeZero d] {A : CountMat n n}
    (x : PrimitivePath A d) : LegalWord A d :=
  restrictWord x.val (primitivePath_period x)

theorem primitiveRestriction_primitive {n d : ℕ} [NeZero d] {A : CountMat n n}
    (x : PrimitivePath A d) : Primitive (primitiveRestriction x).val := by
  apply (cyclicPath_minimalPeriod_iff _ (primitiveRestriction x).property).mp
  rw [show cyclicPath (primitiveRestriction x).val (primitiveRestriction x).property = x.val from
    cyclicPath_restrict x.val (primitivePath_period x)]
  exact x.property

theorem extend_primitiveRestriction {n d : ℕ} [NeZero d] {A : CountMat n n}
    (x : PrimitivePath A d) :
    cyclicPath (primitiveRestriction x).val (primitiveRestriction x).property = x.val :=
  cyclicPath_restrict x.val (primitivePath_period x)

def primitiveWordEquiv {n d : ℕ} [NeZero d] (A : CountMat n n) :
    {a : LegalWord A d // Primitive a.val} ≃ PrimitivePath A d where
  toFun a := ⟨cyclicPath a.val.val a.val.property,
    (cyclicPath_minimalPeriod_iff _ a.val.property).mpr a.property⟩
  invFun x := ⟨primitiveRestriction x,primitiveRestriction_primitive x⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    funext t
    exact cyclicPath_at a.val.val a.val.property t
  right_inv x := Subtype.ext (extend_primitiveRestriction x)

instance primitivePathFintype {n d : ℕ} [NeZero d] (A : CountMat n n) :
    Fintype (PrimitivePath A d) := by
  classical
  exact Fintype.ofEquiv _ (primitiveWordEquiv A)

abbrev LeastLegalWord {n : ℕ} (A : CountMat n n) (d : ℕ) [NeZero d] :=
  {a : LegalWord A d // StrictLeast a.val}

/-- Actual minimal-period PATHS whose original-edge restriction is strictly least. -/
abbrev PathBasis {n : ℕ} (A : CountMat n n) (d : ℕ) [NeZero d] :=
  {x : PrimitivePath A d // StrictLeast (primitiveRestriction x).val}

def basisPathEquiv {n d : ℕ} [NeZero d] (A : CountMat n n) :
    LeastLegalWord A d ≃ PathBasis A d where
  toFun a := ⟨⟨cyclicPath a.val.val a.val.property,
    (cyclicPath_minimalPeriod_iff _ a.val.property).mpr (strictLeast_primitive a.property)⟩,
    by simpa only [primitiveRestriction, restrictWord, cyclicPath_at] using a.property⟩
  invFun x := ⟨primitiveRestriction x.val,x.property⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    funext t
    exact cyclicPath_at a.val.val a.val.property t
  right_inv x := by
    apply Subtype.ext
    exact Subtype.ext (extend_primitiveRestriction x.val)

instance pathBasisFintype {n d : ℕ} [NeZero d] (A : CountMat n n) : Fintype (PathBasis A d) := by
  classical
  exact Fintype.ofEquiv _ (basisPathEquiv A)

/-- Reachability under the ACTUAL forward shift on the actual path carrier. -/
def SamePathOrbit {n d : ℕ} {A : CountMat n n} (x y : PrimitivePath A d) : Prop :=
  ∃ q : ℕ, (shift A)^[q] x.val = y.val

theorem samePathOrbit_iff_rotation {n d : ℕ} [NeZero d] {A : CountMat n n}
    (x y : PrimitivePath A d) : SamePathOrbit x y ↔
      ∃ k : Fin d, rotate k (primitiveRestriction x).val = (primitiveRestriction y).val := by
  constructor
  · rintro ⟨q,hq⟩
    let k : Fin d := ⟨q % d,Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne d))⟩
    refine ⟨k,?_⟩
    apply (cyclicPath_eq_iff _ _
      (rotate_legal _ (primitiveRestriction x).property k) (primitiveRestriction y).property).mp
    rw [cyclicPath_rotate _ (primitiveRestriction x).property k,
      extend_primitiveRestriction, extend_primitiveRestriction]
    change (shift A)^[q % d] x.val = y.val
    rw [(primitivePath_period x).iterate_mod_apply q,hq]
  · rintro ⟨k,hk⟩
    refine ⟨k.val,?_⟩
    calc
      (shift A)^[k.val] x.val = (shift A)^[k.val]
          (cyclicPath (primitiveRestriction x).val (primitiveRestriction x).property) :=
        congrArg ((shift A)^[k.val]) (extend_primitiveRestriction x).symm
      _ = cyclicPath (rotate k (primitiveRestriction x).val)
          (rotate_legal _ (primitiveRestriction x).property k) :=
        (cyclicPath_rotate _ (primitiveRestriction x).property k).symm
      _ = cyclicPath (primitiveRestriction y).val (primitiveRestriction y).property :=
        (cyclicPath_eq_iff _ _ _ _).mpr hk
      _ = y.val := extend_primitiveRestriction y

theorem samePathOrbit_refl {n d : ℕ} {A : CountMat n n} (x : PrimitivePath A d) :
    SamePathOrbit x x := ⟨0,rfl⟩

theorem samePathOrbit_symm {n d : ℕ} [NeZero d] {A : CountMat n n}
    {x y : PrimitivePath A d} (h : SamePathOrbit x y) : SamePathOrbit y x := by
  obtain ⟨k,hk⟩ := (samePathOrbit_iff_rotation x y).mp h
  apply (samePathOrbit_iff_rotation y x).mpr
  refine ⟨-k,?_⟩
  rw [← hk,rotate_negative]

theorem samePathOrbit_trans {n d : ℕ} {A : CountMat n n}
    {x y z : PrimitivePath A d} (hxy : SamePathOrbit x y) (hyz : SamePathOrbit y z) :
    SamePathOrbit x z := by
  obtain ⟨i,hi⟩ := hxy
  obtain ⟨j,hj⟩ := hyz
  refine ⟨j+i,?_⟩
  rw [Function.iterate_add_apply,hi,hj]

def actualPathOrbitSetoid {n d : ℕ} [NeZero d] (A : CountMat n n) :
    Setoid (PrimitivePath A d) where
  r := SamePathOrbit
  iseqv := ⟨samePathOrbit_refl, fun h => samePathOrbit_symm h,
    fun h₁ h₂ => samePathOrbit_trans h₁ h₂⟩

abbrev ActualPathOrbit {n : ℕ} (A : CountMat n n) (d : ℕ) [NeZero d] :=
  Quotient (actualPathOrbitSetoid (d := d) A)

def canonicalPath {n d : ℕ} [NeZero d] {A : CountMat n n}
    (x : PrimitivePath A d) : PathBasis A d :=
  basisPathEquiv A
    ⟨⟨rotate (leastIndex (primitiveRestriction x).val (primitiveRestriction_primitive x))
        (primitiveRestriction x).val,
      rotate_legal _ (primitiveRestriction x).property _⟩,
      leastIndex_spec _ (primitiveRestriction_primitive x)⟩

theorem canonicalPath_eq_shift {n d : ℕ} [NeZero d] {A : CountMat n n}
    (x : PrimitivePath A d) :
    (canonicalPath x).val.val =
      (shift A)^[(leastIndex (primitiveRestriction x).val
        (primitiveRestriction_primitive x)).val] x.val := by
  change cyclicPath
    (rotate (leastIndex (primitiveRestriction x).val (primitiveRestriction_primitive x))
      (primitiveRestriction x).val)
    (rotate_legal _ (primitiveRestriction x).property _) = _
  rw [cyclicPath_rotate _ (primitiveRestriction x).property _, extend_primitiveRestriction]

theorem canonicalPath_sameOrbit {n d : ℕ} [NeZero d] {A : CountMat n n}
    (x : PrimitivePath A d) : SamePathOrbit x (canonicalPath x).val :=
  ⟨_,(canonicalPath_eq_shift x).symm⟩

theorem pathBasis_unique {n d : ℕ} [NeZero d] {A : CountMat n n}
    (b c : PathBasis A d) (h : SamePathOrbit b.val c.val) : b = c := by
  obtain ⟨k,hk⟩ := (samePathOrbit_iff_rotation b.val c.val).mp h
  have hc : StrictLeast (rotate k (primitiveRestriction b.val).val) := hk.symm ▸ c.property
  have hk0 : k = 0 := strictLeast_rotate_index_zero b.property hc
  have he : (primitiveRestriction b.val).val = (primitiveRestriction c.val).val := by
    simpa only [hk0,rotate_zero] using hk
  apply Subtype.ext
  apply Subtype.ext
  rw [← extend_primitiveRestriction b.val, ← extend_primitiveRestriction c.val]
  exact (cyclicPath_eq_iff _ _ _ _).mpr he

theorem canonicalPath_of_basis {n d : ℕ} [NeZero d] {A : CountMat n n}
    (b : PathBasis A d) : canonicalPath b.val = b :=
  pathBasis_unique _ _ (samePathOrbit_symm (canonicalPath_sameOrbit b.val))

theorem canonicalPath_eq_of_sameOrbit {n d : ℕ} [NeZero d] {A : CountMat n n}
    {x y : PrimitivePath A d} (h : SamePathOrbit x y) : canonicalPath x = canonicalPath y :=
  pathBasis_unique _ _ (samePathOrbit_trans
    (samePathOrbit_symm (canonicalPath_sameOrbit x))
    (samePathOrbit_trans h (canonicalPath_sameOrbit y)))

/-- A genuine quotient of original primitive PATHS, with a proved basis.
No nonemptiness of the quotient or the basis is required. -/
def orbitBasisEquiv {n d : ℕ} [NeZero d] (A : CountMat n n) :
    ActualPathOrbit A d ≃ PathBasis A d where
  toFun := Quotient.lift canonicalPath (fun _ _ h => canonicalPath_eq_of_sameOrbit h)
  invFun b := Quotient.mk (actualPathOrbitSetoid A) b.val
  left_inv o := by
    refine Quotient.inductionOn o ?_
    intro x
    exact Quotient.sound (samePathOrbit_symm (canonicalPath_sameOrbit x))
  right_inv := canonicalPath_of_basis

instance actualPathOrbitFintype {n d : ℕ} [NeZero d] (A : CountMat n n) :
    Fintype (ActualPathOrbit A d) :=
  Fintype.ofEquiv _ (orbitBasisEquiv A).symm

/-! Exact elementary recoding on periodic primitive paths and their orbits. -/

def elementaryPrimitiveEquiv {n m d : ℕ} (R : CountMat n m) (S : CountMat m n) :
    PrimitivePath (R*S) d ≃ PrimitivePath (S*R) d where
  toFun x := ⟨elementaryHomeomorph R S x.val, by rw [elementary_minimalPeriod,x.property]⟩
  invFun y := ⟨(elementaryHomeomorph R S).symm y.val, by
    have h := elementary_minimalPeriod R S ((elementaryHomeomorph R S).symm y.val)
    rw [(elementaryHomeomorph R S).apply_symm_apply,y.property] at h
    exact h.symm⟩
  left_inv x := Subtype.ext ((elementaryHomeomorph R S).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((elementaryHomeomorph R S).apply_symm_apply y.val)

theorem elementary_samePathOrbit_iff {n m d : ℕ} (R : CountMat n m) (S : CountMat m n)
    (x y : PrimitivePath (R*S) d) :
    SamePathOrbit (elementaryPrimitiveEquiv R S x) (elementaryPrimitiveEquiv R S y) ↔
      SamePathOrbit x y := by
  have hs : Function.Semiconj (elementaryHomeomorph R S) (shift (R*S)) (shift (S*R)) :=
    elementary_shift R S
  constructor
  · rintro ⟨q,hq⟩
    refine ⟨q,(elementaryHomeomorph R S).injective ?_⟩
    rw [hs.iterate_right q x.val]
    exact hq
  · rintro ⟨q,hq⟩
    refine ⟨q,?_⟩
    change (shift (S*R))^[q] (elementaryHomeomorph R S x.val) =
      elementaryHomeomorph R S y.val
    rw [← hs.iterate_right q x.val,hq]

def elementaryOrbitEquiv {n m d : ℕ} [NeZero d]
    (R : CountMat n m) (S : CountMat m n) :
    ActualPathOrbit (R*S) d ≃ ActualPathOrbit (S*R) d where
  toFun := Quotient.map (elementaryPrimitiveEquiv R S)
    (fun x y h => (elementary_samePathOrbit_iff R S x y).mpr h)
  invFun := Quotient.map (elementaryPrimitiveEquiv R S).symm (by
    intro x y h
    change SamePathOrbit x y at h
    change SamePathOrbit ((elementaryPrimitiveEquiv R S).symm x)
      ((elementaryPrimitiveEquiv R S).symm y)
    apply (elementary_samePathOrbit_iff R S _ _).mp
    simpa only [Equiv.apply_symm_apply] using h)
  left_inv o := by
    refine Quotient.inductionOn o ?_
    intro x
    change Quotient.mk _ ((elementaryPrimitiveEquiv R S).symm
      (elementaryPrimitiveEquiv R S x)) = Quotient.mk _ x
    rw [Equiv.symm_apply_apply]
  right_inv o := by
    refine Quotient.inductionOn o ?_
    intro x
    change Quotient.mk _ (elementaryPrimitiveEquiv R S
      ((elementaryPrimitiveEquiv R S).symm x)) = Quotient.mk _ x
    rw [Equiv.apply_symm_apply]

def canonicalForwardOffset {n d : ℕ} [NeZero d] {A : CountMat n n}
    (x : PrimitivePath A d) : Fin d :=
  -leastIndex (primitiveRestriction x).val (primitiveRestriction_primitive x)

theorem canonicalForwardOffset_equation {n d : ℕ} [NeZero d] {A : CountMat n n}
    (x : PrimitivePath A d) :
    x.val = (shift A)^[(canonicalForwardOffset x).val] (canonicalPath x).val.val := by
  let a := primitiveRestriction x
  let k := leastIndex a.val (primitiveRestriction_primitive x)
  change x.val = (shift A)^[(-k).val]
    (cyclicPath (rotate k a.val) (rotate_legal a.val a.property k))
  calc
    x.val = cyclicPath a.val a.property := (extend_primitiveRestriction x).symm
    _ = cyclicPath (rotate (-k) (rotate k a.val))
        (rotate_legal _ (rotate_legal a.val a.property k) (-k)) :=
      (cyclicPath_eq_iff _ _ _ _).mpr (rotate_negative k a.val).symm
    _ = (shift A)^[(-k).val]
        (cyclicPath (rotate k a.val) (rotate_legal a.val a.property k)) :=
      cyclicPath_rotate _ (rotate_legal a.val a.property k) (-k)

/-- Every actual primitive orbit has exactly its period's worth of forward phases,
including when the graph or the primitive stratum is empty. -/
theorem primitivePath_card_eq_period_mul_orbit_card {n : ℕ}
    (A : CountMat n n) (d : ℕ) [NeZero d] :
    Fintype.card (PrimitivePath A d) = d * Fintype.card (ActualPathOrbit A d) := by
  let e : PrimitivePath A d ≃ PathBasis A d × Fin d := by
    let move (b : PathBasis A d) (q : Fin d) : PrimitivePath A d :=
      ⟨(shift A)^[q.val] b.val.val, by
        rw [Function.minimalPeriod_apply_iterate
          (Function.mk_mem_periodicPts (Nat.pos_of_ne_zero (NeZero.ne d))
            (primitivePath_period b.val)), b.val.property]⟩
    refine {
      toFun := fun x => (canonicalPath x, canonicalForwardOffset x)
      invFun := fun y => move y.1 y.2
      left_inv := ?_
      right_inv := ?_ }
    · intro x
      exact Subtype.ext (canonicalForwardOffset_equation x).symm
    · rintro ⟨b, q⟩
      have hb : SamePathOrbit b.val (move b q) := ⟨q.val, rfl⟩
      have hc : canonicalPath (move b q) = b :=
        (canonicalPath_eq_of_sameOrbit hb).symm.trans (canonicalPath_of_basis b)
      apply Prod.ext
      · exact hc
      · apply Fin.ext
        have hp := (canonicalPath (move b q)).val.property
        apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
          (f := shift A) (x := (canonicalPath (move b q)).val.val)
          (m := (canonicalForwardOffset (move b q)).val) (n := q.val)
          (by simpa only [hp] using (canonicalForwardOffset (move b q)).isLt)
          (by simpa only [hp] using q.isLt)).mp
        calc
          _ = (move b q).val := (canonicalForwardOffset_equation (move b q)).symm
          _ = _ := by rw [hc]
  calc
    Fintype.card (PrimitivePath A d) = Fintype.card (PathBasis A d × Fin d) :=
      Fintype.card_congr e
    _ = Fintype.card (PathBasis A d) * d := by
      rw [Fintype.card_prod, Fintype.card_fin]
    _ = d * Fintype.card (ActualPathOrbit A d) := by
      rw [← Fintype.card_congr (orbitBasisEquiv A), Nat.mul_comm]

open scoped Fin.NatCast in
theorem finEquiv_eq_natCast {d : ℕ} [NeZero d] (k : Fin d) :
    ZMod.finEquiv d k = (k.val : ZMod d) := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ d =>
    change k = (k.val : Fin (d+1))
    exact (Fin.cast_val_eq_self k).symm

theorem canonicalForwardOffset_residue {n d : ℕ} [NeZero d] {A : CountMat n n}
    (x : PrimitivePath A d) :
    ZMod.finEquiv d (canonicalForwardOffset x) =
      ((-((leastIndex (primitiveRestriction x).val
        (primitiveRestriction_primitive x)).val : ℤ)) : ZMod d) := by
  rw [canonicalForwardOffset,map_neg,finEquiv_eq_natCast]
  simp only [Int.cast_neg,Int.cast_natCast]

/-- Relative FORWARD gyration for the exact elementaryHomeomorph and the
canonical original-graph bases. Its index is the actual primitive PATH quotient.
Each term recodes its original source basis representative and uses the
actual target forward offset from canonicalForwardOffset_equation. -/
def relativeForwardGyration {n m d : ℕ} [NeZero d]
    (R : CountMat n m) (S : CountMat m n) : ZMod d :=
  ∑ o : ActualPathOrbit (R*S) d,
    ZMod.finEquiv d (canonicalForwardOffset
      (elementaryPrimitiveEquiv R S ((orbitBasisEquiv (R*S)) o).val))

/-! Reindex the actual orbit sum through the TWO proved inverses. -/

def recodeWord {n m d : ℕ} [NeZero d] (z : Entry n m → ℕ)
    (a : LegalWord (rMatrix z * sMatrix z) d) :
    LegalWord (sMatrix z * rMatrix z) d :=
  let p := (numberedWordEquiv z).symm a
  ⟨targetEdge p.1 z p.2,targetEdge_legal p.1 z p.2⟩

theorem recodeWord_numberedWord {n m d : ℕ} [NeZero d] (z : Entry n m → ℕ)
    (p : Σ w : VertexWord n m d, Labels w z) :
    (recodeWord z (numberedWord z p)).val = targetEdge p.1 z p.2 := by
  change targetEdge ((numberedWordEquiv z).symm ((numberedWordEquiv z) p)).1 z
    ((numberedWordEquiv z).symm ((numberedWordEquiv z) p)).2 = _
  rw [Equiv.symm_apply_apply]

theorem recodeWord_path {n m d : ℕ} [NeZero d] (z : Entry n m → ℕ)
    (a : LegalWord (rMatrix z * sMatrix z) d) :
    elementaryHomeomorph (rMatrix z) (sMatrix z) (cyclicPath a.val a.property) =
      cyclicPath (recodeWord z a).val (recodeWord z a).property := by
  let p := (numberedWordEquiv z).symm a
  have ha : numberedWord z p = a := (numberedWordEquiv z).apply_symm_apply a
  have he := elementary_source_cyclicPath p.1 z p.2
  change elementaryHomeomorph _ _ (cyclicPath (numberedWord z p).val
    (numberedWord z p).property) = _ at he
  change elementaryHomeomorph _ _ (cyclicPath a.val a.property) =
    cyclicPath (targetEdge p.1 z p.2) (targetEdge_legal p.1 z p.2)
  simpa only [ha] using he

theorem recodeWord_primitive_iff {n m d : ℕ} [NeZero d] (z : Entry n m → ℕ)
    (a : LegalWord (rMatrix z * sMatrix z) d) :
    Primitive (recodeWord z a).val ↔ Primitive a.val := by
  rw [← cyclicPath_minimalPeriod_iff _ (recodeWord z a).property,
    ← cyclicPath_minimalPeriod_iff _ a.property,← recodeWord_path z a,
    elementary_minimalPeriod]

theorem target_primitiveRestriction {n m d : ℕ} [NeZero d] (z : Entry n m → ℕ)
    (a : LeastLegalWord (rMatrix z * sMatrix z) d) :
    (primitiveRestriction (elementaryPrimitiveEquiv (rMatrix z) (sMatrix z)
      ((basisPathEquiv (rMatrix z * sMatrix z)) a).val)).val =
        (recodeWord z a.val).val := by
  funext t
  have h := congrArg (fun x : Path (sMatrix z * rMatrix z) => x.val (t.val : ℤ))
    (recodeWord_path z a.val)
  change (elementaryHomeomorph (rMatrix z) (sMatrix z)
    (cyclicPath a.val.val a.val.property)).val (t.val : ℤ) = _
  simpa only [cyclicPath_at] using h

theorem wordWeight_eq_negative_leastIndex {n m d : ℕ} [NeZero d]
    {A : CountMat n n} {B : CountMat m m} (a : Fin d → Edge A) (b : Fin d → Edge B)
    (ha : StrictLeast a) (hb : Primitive b) :
    wordWeight a b = -((leastIndex b hb).val : ℤ) := by
  classical
  rw [wordWeight,if_pos ha]
  rw [Finset.sum_eq_single (leastIndex b hb)]
  · exact if_pos (leastIndex_spec b hb)
  · intro k _ hk
    apply if_neg
    intro h
    exact hk (leastIndex_unique b hb k h)
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem orbit_summand_eq_wordWeight {n m d : ℕ} [NeZero d] (z : Entry n m → ℕ)
    (a : LeastLegalWord (rMatrix z * sMatrix z) d) :
    ZMod.finEquiv d (canonicalForwardOffset
      (elementaryPrimitiveEquiv (rMatrix z) (sMatrix z)
        ((basisPathEquiv (rMatrix z * sMatrix z)) a).val)) =
      ((wordWeight a.val.val (recodeWord z a.val).val : ℤ) : ZMod d) := by
  have hb : Primitive (recodeWord z a.val).val :=
    (recodeWord_primitive_iff z a.val).mpr (strictLeast_primitive a.property)
  have hi : leastIndex
      (primitiveRestriction (elementaryPrimitiveEquiv (rMatrix z) (sMatrix z)
        ((basisPathEquiv (rMatrix z * sMatrix z)) a).val)).val
      (primitiveRestriction_primitive _) = leastIndex (recodeWord z a.val).val hb := by
    apply leastIndex_unique (recodeWord z a.val).val hb
    have h := leastIndex_spec
      (primitiveRestriction (elementaryPrimitiveEquiv (rMatrix z) (sMatrix z)
        ((basisPathEquiv (rMatrix z * sMatrix z)) a).val)).val
      (primitiveRestriction_primitive _)
    simpa only [target_primitiveRestriction z a] using h
  rw [canonicalForwardOffset_residue,hi,
    wordWeight_eq_negative_leastIndex _ _ a.property hb]
  simp only [Int.cast_neg, Int.cast_natCast]

theorem relativeForwardGyration_eq_word_sum {n m d : ℕ} [NeZero d]
    (z : Entry n m → ℕ) :
    relativeForwardGyration (d := d) (rMatrix z) (sMatrix z) =
      ((∑ a : LegalWord (rMatrix z * sMatrix z) d,
        wordWeight a.val (recodeWord z a).val : ℤ) : ZMod d) := by
  classical
  let W : LegalWord (rMatrix z * sMatrix z) d → ℤ :=
    fun a => wordWeight a.val (recodeWord z a).val
  have hsub : (∑ a : LegalWord (rMatrix z * sMatrix z) d, W a) =
      ∑ a : LeastLegalWord (rMatrix z * sMatrix z) d, W a.val := by
    apply Finset.sum_congr_set {a | StrictLeast a.val} W (fun a => W a.val)
    · intro a _; rfl
    · intro a ha
      change (if StrictLeast a.val then _ else (0 : ℤ)) = 0
      exact if_neg ha
  calc
    relativeForwardGyration (rMatrix z) (sMatrix z) =
        ∑ b : PathBasis (rMatrix z * sMatrix z) d,
          ZMod.finEquiv d (canonicalForwardOffset
            (elementaryPrimitiveEquiv (rMatrix z) (sMatrix z) b.val)) :=
      (orbitBasisEquiv (rMatrix z * sMatrix z)).sum_comp
        (fun b => ZMod.finEquiv d (canonicalForwardOffset
          (elementaryPrimitiveEquiv (rMatrix z) (sMatrix z) b.val)))
    _ = ∑ a : LeastLegalWord (rMatrix z * sMatrix z) d,
          ZMod.finEquiv d (canonicalForwardOffset
            (elementaryPrimitiveEquiv (rMatrix z) (sMatrix z)
              ((basisPathEquiv (rMatrix z * sMatrix z)) a).val)) :=
      ((basisPathEquiv (rMatrix z * sMatrix z)).sum_comp _).symm
    _ = ∑ a : LeastLegalWord (rMatrix z * sMatrix z) d, (W a.val : ZMod d) := by
      apply Finset.sum_congr rfl
      intro a _
      exact orbit_summand_eq_wordWeight z a
    _ = ((∑ a : LeastLegalWord (rMatrix z * sMatrix z) d, W a.val : ℤ) : ZMod d) := by
      simp only [Int.cast_sum]
    _ = ((∑ a : LegalWord (rMatrix z * sMatrix z) d, W a : ℤ) : ZMod d) :=
      congrArg (fun v : ℤ => (v : ZMod d)) hsub.symm

/-- Finite index independent of matrix-entry magnitudes; unchanged rank-word
weight and product-choose factors from the immutable input. -/
def orderTypeGyrationLift {n m d : ℕ} [NeZero d] (z : Entry n m → ℕ) : ℤ :=
  ∑ w : VertexWord n m d, ∑ T : WordType w,
    wordWeight (sourceEdge w (widths T) (rankLabels T))
      (targetEdge w (widths T) (rankLabels T)) *
      (∏ e : Entry n m, Nat.choose (z e) (widths T e) : ℕ)

/-- The actual primitive-PATH-orbit forward-offset sum equals the numbered
order-type sum for EVERY nonnegative finite pair and EVERY positive period.
All four identifications are proved above; none is a premise of this theorem. -/
theorem relativeForwardGyration_eq_order_types {n m d : ℕ} [NeZero d]
    (z : Entry n m → ℕ) :
    relativeForwardGyration (d := d) (rMatrix z) (sMatrix z) =
      (orderTypeGyrationLift (d := d) z : ZMod d) := by
  classical
  rw [relativeForwardGyration_eq_word_sum]
  apply congrArg (fun v : ℤ => (v : ZMod d))
  calc
    (∑ a : LegalWord (rMatrix z * sMatrix z) d,
        wordWeight a.val (recodeWord z a).val) =
        ∑ p : (Σ w : VertexWord n m d, Labels w z),
          wordWeight (sourceEdge p.1 z p.2) (targetEdge p.1 z p.2) := by
      calc
        _ = ∑ p : (Σ w : VertexWord n m d, Labels w z),
            wordWeight ((numberedWordEquiv z) p).val
              (recodeWord z ((numberedWordEquiv z) p)).val :=
          ((numberedWordEquiv (d := d) z).sum_comp
            (fun a => wordWeight a.val (recodeWord z a).val)).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro p _
          change wordWeight (sourceEdge p.1 z p.2)
            (recodeWord z (numberedWord z p)).val = _
          rw [recodeWord_numberedWord]
    _ = ∑ w : VertexWord n m d, ∑ l : Labels w z,
        wordWeight (sourceEdge w z l) (targetEdge w z l) := Fintype.sum_sigma _
    _ = orderTypeGyrationLift z := by
      apply Finset.sum_congr rfl
      intro w _
      exact numbered_word_sum_eq_order_types w z

end D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
