/- GID: D5/S3/ConceptDynamics/Coding/CountedOrderTypeGyration
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedOrderTypeGyration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original counted orbits, order types, and integral polynomial lifts. -/

import D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
import D5.S3.ConceptDynamics.Coding.FixedBlockRigidity.BlockCoordinates
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Classical

namespace D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration

open scoped BigOperators
open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap

/-! The entrywise realization equivalence. These definitions are consumed below
by occurrences of R/S half-edges in the actual numbered recoding. -/

abbrev Increasing (z k : ℕ) := {f : Fin k → Fin z // StrictMono f}

abbrev Selection (z k : ℕ) := {s : Finset (Fin z) // s.card = k}

def selectionMap {z k : ℕ} (s : Selection z k) : Increasing z k :=
  ⟨s.val.orderEmbOfFin s.property, (s.val.orderEmbOfFin s.property).strictMono⟩

theorem selectionMap_bijective (z k : ℕ) :
    Function.Bijective (@selectionMap z k) := by
  classical
  constructor
  · intro s t h
    apply Subtype.ext
    have he : (s.val.orderEmbOfFin s.property : Fin k → Fin z) =
        t.val.orderEmbOfFin t.property := congrArg Subtype.val h
    calc
      s.val = Finset.image (s.val.orderEmbOfFin s.property) Finset.univ :=
        (Finset.image_orderEmbOfFin_univ _ _).symm
      _ = Finset.image (t.val.orderEmbOfFin t.property) Finset.univ := by rw [he]
      _ = t.val := Finset.image_orderEmbOfFin_univ _ _
  · intro f
    let s : Finset (Fin z) := Finset.image f.val Finset.univ
    have hs : s.card = k := by
      simp [s, Finset.card_image_of_injective _ f.property.injective]
    refine ⟨⟨s, hs⟩, ?_⟩
    apply Subtype.ext
    exact (Finset.orderEmbOfFin_unique hs
      (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)) f.property).symm

def selectionEquiv (z k : ℕ) : Selection z k ≃ Increasing z k :=
  Equiv.ofBijective selectionMap (selectionMap_bijective z k)

theorem increasing_card (z k : ℕ) :
    Fintype.card (Increasing z k) = Nat.choose z k := by
  classical
  let e : Selection z k ≃ ↥((Finset.univ : Finset (Fin z)).powersetCard k) :=
    Equiv.subtypeEquivRight (fun s => by simp [Finset.mem_powersetCard])
  rw [← Fintype.card_congr (selectionEquiv z k), Fintype.card_congr e]
  simp

/-- A finite ordered partition of O, including the unique empty partition.
The bound is part of the finite index, not a bound on a matrix entry. -/
abbrev Pattern (O : Type*) [Fintype O] :=
  Σ k : Fin (Fintype.card O + 1), {r : O → Fin k.val // Function.Surjective r}

abbrev Realization {O : Type*} [Fintype O] (T : Pattern O) (z : ℕ) :=
  Increasing z T.1.val

def realize {O : Type*} [Fintype O] {z : ℕ}
    (p : Σ T : Pattern O, Realization T z) : O → Fin z :=
  fun a => p.2.val (p.1.2.val a)

private theorem image_comp_surjective {O : Type*} [Fintype O]
    {k z : ℕ} (r : O → Fin k) (hr : Function.Surjective r) (f : Fin k → Fin z) :
    Finset.image (fun a => f (r a)) Finset.univ = Finset.image f Finset.univ := by
  classical
  ext b
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨r a, ha⟩
  · rintro ⟨i, hi⟩
    obtain ⟨a, rfl⟩ := hr i
    exact ⟨a, hi⟩

theorem realize_bijective (O : Type*) [Fintype O] (z : ℕ) :
    Function.Bijective (@realize O _ z) := by
  classical
  constructor
  · rintro ⟨⟨⟨k, hk⟩, r, hr⟩, u, hu⟩ ⟨⟨⟨l, hl⟩, s, hs⟩, v, hv⟩ h
    change (fun a => u (r a)) = (fun a => v (s a)) at h
    have himage : Finset.image u Finset.univ = Finset.image v Finset.univ := by
      rw [← image_comp_surjective r hr u, ← image_comp_surjective s hs v, h]
    have hkl : k = l := by
      have hc := congrArg Finset.card himage
      simpa only [Finset.card_image_of_injective _ hu.injective,
        Finset.card_image_of_injective _ hv.injective,
        Finset.card_univ, Fintype.card_fin] using hc
    subst l
    have huv : u = v := by
      apply (hu.range_inj hv).mp
      have hc := congrArg (fun s : Finset (Fin z) => (s : Set (Fin z))) himage
      simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using hc
    subst v
    have hrs : r = s := by
      funext a
      exact hu.injective (congrFun h a)
    subst s
    rfl
  · intro f
    let image : Finset (Fin z) := Finset.image f Finset.univ
    let k := image.card
    have hk : k < Fintype.card O + 1 := by
      have hle : image.card ≤ Fintype.card O := by
        simpa only [Finset.card_univ] using (Finset.card_image_le (s := Finset.univ) (f := f))
      exact Nat.lt_succ_of_le hle
    let q : O → image := fun a => ⟨f a, Finset.mem_image_of_mem _ (Finset.mem_univ a)⟩
    have hq : Function.Surjective q := by
      intro b
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp b.property
      exact ⟨a, Subtype.ext ha⟩
    let order : Fin k ≃o image := image.orderIsoOfFin rfl
    let r : O → Fin k := fun a => order.symm (q a)
    have hr : Function.Surjective r := order.symm.surjective.comp hq
    let T : Pattern O := ⟨⟨k, hk⟩, ⟨r, hr⟩⟩
    refine ⟨⟨T, selectionMap ⟨image, rfl⟩⟩, ?_⟩
    funext a
    change (order (order.symm (q a))).val = f a
    exact congrArg Subtype.val (order.apply_symm_apply (q a))

/-- Its forward direction inserts selected labels in their rank classes.
The inverse is determined by the finite image and its increasing enumeration. -/
def realizationEquiv (O : Type*) [Fintype O] (z : ℕ) :
    (Σ T : Pattern O, Realization T z) ≃ (O → Fin z) :=
  Equiv.ofBijective realize (realize_bijective O z)

theorem realization_card {O : Type*} [Fintype O] (T : Pattern O) (z : ℕ) :
    Fintype.card (Realization T z) = Nat.choose z T.1.val :=
  increasing_card z T.1.val

/-! The pinned fiberEquiv order, rather than an arbitrary numbering. -/

abbrev OrderedFiber {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (i k : Fin n) := Lex (Σ j : Fin m, Lex (Fin (R i j) × Fin (S j k)))

def fiberKey {n m : ℕ} {R : CountMat n m} {S : CountMat m n}
    {i k : Fin n} (p : Fiber R S i k) : OrderedFiber R S i k :=
  toLex ⟨p.1, toLex p.2⟩

theorem fiber_number_lt_iff {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (i k : Fin n) (p q : Fiber R S i k) :
    (fiberEquiv R S i k).symm p < (fiberEquiv R S i k).symm q ↔
      fiberKey p < fiberKey q := by
  classical
  let ordered : OrderedFiber R S i k ≃ Fiber R S i k :=
    ofLex.trans (Equiv.sigmaCongrRight fun _ => ofLex)
  have hcard : Fintype.card (Fiber R S i k) = (R * S) i k := by
    simp [Fiber, Matrix.mul_apply, Fintype.card_sigma, Fintype.card_prod]
  let rank : Fin ((R * S) i k) ≃o OrderedFiber R S i k :=
    Fintype.orderIsoFinOfCardEq _ ((Fintype.card_congr ordered).trans hcard)
  change rank.symm (fiberKey p) < rank.symm (fiberKey q) ↔ fiberKey p < fiberKey q
  exact rank.symm.lt_iff_lt

/-- The original edge order: source, target, then its canonical number. -/
def EdgeLT {n m : ℕ} {M : CountMat n m} (a b : Edge M) : Prop :=
  a.source < b.source ∨ a.source = b.source ∧
    (a.target < b.target ∨ a.target = b.target ∧ a.number.val < b.number.val)

abbrev EntryEmbedding {n m : ℕ} (R R' : CountMat n m) :=
  ∀ i j, Fin (R i j) ↪o Fin (R' i j)

def relabelFiber {n m : ℕ} {R R' : CountMat n m} {S S' : CountMat m n}
    (f : EntryEmbedding R R') (g : EntryEmbedding S S') {i k : Fin n}
    (p : Fiber R S i k) : Fiber R' S' i k :=
  ⟨p.1, f i p.1 p.2.1, g p.1 k p.2.2⟩

def relabelEdge {n m : ℕ} {R R' : CountMat n m} {S S' : CountMat m n}
    (f : EntryEmbedding R R') (g : EntryEmbedding S S') (a : Edge (R * S)) :
    Edge (R' * S') :=
  ⟨a.source, a.target, (fiberEquiv R' S' a.source a.target).symm
    (relabelFiber f g (fiberEquiv R S a.source a.target a.number))⟩

theorem relabelEdge_injective {n m : ℕ} {R R' : CountMat n m} {S S' : CountMat m n}
    (f : EntryEmbedding R R') (g : EntryEmbedding S S') :
    Function.Injective (relabelEdge f g) := by
  intro a b h
  rcases a with ⟨i, k, a⟩
  rcases b with ⟨i', k', b⟩
  have hi : i = i' := congrArg Edge.source h
  have hk : k = k' := congrArg Edge.target h
  subst i'
  subst k'
  have hn : (relabelEdge f g (⟨i,k,a⟩ : Edge (R*S))).number =
      (relabelEdge f g (⟨i,k,b⟩ : Edge (R*S))).number :=
    Fin.ext (congrArg (fun e => e.number.val) h)
  have hp : relabelFiber f g (fiberEquiv R S i k a) =
      relabelFiber f g (fiberEquiv R S i k b) :=
    (fiberEquiv R' S' i k).symm.injective hn
  have hinj : Function.Injective (@relabelFiber n m R R' S S' f g i k) := by
    rintro ⟨j,r,s⟩ ⟨j',r',s'⟩ h
    have hj : j = j' := congrArg Sigma.fst h
    subst j'
    have hrs : (f i j r, g j k s) = (f i j r', g j k s') :=
      by simpa only [relabelFiber, Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
    have hr : r = r' := (f i j).injective (congrArg Prod.fst hrs)
    have hs : s = s' := (g j k).injective (congrArg Prod.snd hrs)
    subst r'
    subst s'
    rfl
  have hab : a = b := (fiberEquiv R S i k).injective (hinj hp)
  subst b
  rfl

theorem relabelEdge_lt_iff {n m : ℕ} {R R' : CountMat n m} {S S' : CountMat m n}
    (f : EntryEmbedding R R') (g : EntryEmbedding S S') (a b : Edge (R * S)) :
    EdgeLT (relabelEdge f g a) (relabelEdge f g b) ↔ EdgeLT a b := by
  rcases a with ⟨i,k,a⟩
  rcases b with ⟨i',k',b⟩
  by_cases hi : i = i'
  · subst i'
    by_cases hk : k = k'
    · subst k'
      let p := fiberEquiv R S i k a
      let q := fiberEquiv R S i k b
      have ha : a = (fiberEquiv R S i k).symm p :=
        ((fiberEquiv R S i k).symm_apply_apply a).symm
      have hb : b = (fiberEquiv R S i k).symm q :=
        ((fiberEquiv R S i k).symm_apply_apply b).symm
      have hc :
          (fiberEquiv R' S' i k).symm (relabelFiber f g p) <
              (fiberEquiv R' S' i k).symm (relabelFiber f g q) ↔ a < b := by
        rw [ha, hb, fiber_number_lt_iff, fiber_number_lt_iff]
        rcases p with ⟨j,r,s⟩
        rcases q with ⟨j',r',s'⟩
        dsimp only [relabelFiber, fiberKey, toLex]
        by_cases hj : j = j'
        · subst j'
          simp only [Sigma.Lex.lt_def]
          change (j < j ∨ ∃ h : j = j,
            h ▸ (toLex ((f i j) r, (g j k) s) : Lex _) <
              toLex ((f i j) r', (g j k) s')) ↔
            (j < j ∨ ∃ h : j = j, h ▸ (toLex (r, s) : Lex _) < toLex (r', s'))
          simp [Prod.Lex.toLex_lt_toLex, (f i j).lt_iff_lt,
            (f i j).injective.eq_iff, (g j k).lt_iff_lt]
        · simp only [Sigma.Lex.lt_def]
          change (j < j' ∨ ∃ h : j = j',
            h ▸ (toLex ((f i j) r, (g j k) s) : Lex _) <
              toLex ((f i j') r', (g j' k) s')) ↔
            (j < j' ∨ ∃ h : j = j', h ▸ (toLex (r, s) : Lex _) < toLex (r', s'))
          simp [hj]
      simpa only [EdgeLT, relabelEdge, lt_self_iff_false, false_or,
        true_and, Fin.lt_def] using hc
    · simp [EdgeLT, relabelEdge, hk]
  · simp [EdgeLT, relabelEdge, hi]

theorem relabelEdge_join {n m : ℕ} {R R' : CountMat n m} {S S' : CountMat m n}
    (f : EntryEmbedding R R') (g : EntryEmbedding S S')
    (i k : Fin n) (j : Fin m) (r : Fin (R i j)) (s : Fin (S j k)) :
    relabelEdge f g (join R S ⟨i,j,r⟩ ⟨j,k,s⟩ rfl) =
      join R' S' ⟨i,j,f i j r⟩ ⟨j,k,g j k s⟩ rfl := by
  dsimp only [relabelEdge, join]
  rw [Equiv.apply_symm_apply]
  rfl

/-! Actual legal histories and the actual elementaryHomeomorph. -/

theorem elementary_coordinate {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (x : Path (R * S)) (t : ℤ) :
    (elementaryHomeomorph R S x).val t =
      join S R (split R S (x.val t)).2 (split R S (x.val (t+1))).1
        (x.property t) := by
  rfl

theorem elementary_shift {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (x : Path (R * S)) :
    elementaryHomeomorph R S (shift (R*S) x) =
      shift (S*R) (elementaryHomeomorph R S x) := by
  apply Subtype.ext
  rfl

theorem elementary_period_iff {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (x : Path (R * S)) (d : ℕ) :
    Function.IsPeriodicPt (shift (S*R)) d (elementaryHomeomorph R S x) ↔
      Function.IsPeriodicPt (shift (R*S)) d x := by
  have hs : Function.Semiconj (elementaryHomeomorph R S) (shift (R*S)) (shift (S*R)) :=
    elementary_shift R S
  change (shift (S*R))^[d] (elementaryHomeomorph R S x) = elementaryHomeomorph R S x ↔
    (shift (R*S))^[d] x = x
  rw [← hs.iterate_right d x]
  exact (elementaryHomeomorph R S).injective.eq_iff

theorem elementary_minimalPeriod {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (x : Path (R * S)) :
    Function.minimalPeriod (shift (S*R)) (elementaryHomeomorph R S x) =
      Function.minimalPeriod (shift (R*S)) x := by
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro d
  exact elementary_period_iff R S x d

/-! Finite words here consist of ACTUAL numbered product edges. Fin d indexes
their time coordinates; it is not a replacement of their edge alphabet. -/

def WordLT {n d : ℕ} {A : CountMat n n} (x y : Fin d → Edge A) : Prop :=
  ∃ t : Fin d, (∀ u : Fin d, u < t → x u = y u) ∧ EdgeLT (x t) (y t)

def rotate {d : ℕ} [NeZero d] {α : Type*} (k : Fin d) (x : Fin d → α) : Fin d → α :=
  fun t => x (t+k)

def StrictLeast {n d : ℕ} [NeZero d] {A : CountMat n n} (x : Fin d → Edge A) : Prop :=
  ∀ k : Fin d, k ≠ 0 → WordLT x (rotate k x)

def Primitive {d : ℕ} [NeZero d] {α : Type*} (x : Fin d → α) : Prop :=
  ∀ k : Fin d, k ≠ 0 → rotate k x ≠ x

theorem strictLeast_primitive {n d : ℕ} [NeZero d] {A : CountMat n n}
    {x : Fin d → Edge A} (hx : StrictLeast x) : Primitive x := by
  intro k hk heq
  obtain ⟨t, _, hlt⟩ := hx k hk
  rw [heq] at hlt
  simp [EdgeLT] at hlt

theorem rotate_negative {d : ℕ} [NeZero d] {α : Type*}
    (k : Fin d) (x : Fin d → α) : rotate (-k) (rotate k x) = x := by
  funext t
  simp [rotate, add_assoc]

theorem wordLT_relabel_iff {n m d : ℕ} {R R' : CountMat n m} {S S' : CountMat m n}
    (f : EntryEmbedding R R') (g : EntryEmbedding S S') (x y : Fin d → Edge (R*S)) :
    WordLT (fun t => relabelEdge f g (x t)) (fun t => relabelEdge f g (y t)) ↔
      WordLT x y := by
  constructor
  · rintro ⟨t, hp, ht⟩
    exact ⟨t, fun u hu => relabelEdge_injective f g (hp u hu),
      (relabelEdge_lt_iff f g (x t) (y t)).mp ht⟩
  · rintro ⟨t, hp, ht⟩
    exact ⟨t, fun u hu => congrArg (relabelEdge f g) (hp u hu),
      (relabelEdge_lt_iff f g (x t) (y t)).mpr ht⟩

theorem strictLeast_relabel_iff {n m d : ℕ} [NeZero d]
    {R R' : CountMat n m} {S S' : CountMat m n}
    (f : EntryEmbedding R R') (g : EntryEmbedding S S') (x : Fin d → Edge (R*S)) :
    StrictLeast (fun t => relabelEdge f g (x t)) ↔ StrictLeast x := by
  unfold StrictLeast
  apply forall_congr'
  intro k
  exact imp_congr_right (fun _ => wordLT_relabel_iff f g x (rotate k x))

/-- Each summand is the forward offset -k, when the source word is least and
the k-th forward rotation of the target word is least. No orbit-count premise. -/
def wordWeight {n m d : ℕ} [NeZero d] {A : CountMat n n} {B : CountMat m m}
    (a : Fin d → Edge A) (b : Fin d → Edge B) : ℤ := by
  classical
  exact if StrictLeast a then
    ∑ k : Fin d, if StrictLeast (rotate k b) then -(k.val : ℤ) else 0
  else 0

theorem wordWeight_relabel {n m d : ℕ} [NeZero d]
    {R R' : CountMat n m} {S S' : CountMat m n}
    (f : EntryEmbedding R R') (g : EntryEmbedding S S')
    (a : Fin d → Edge (R*S)) (b : Fin d → Edge (S*R)) :
    wordWeight (fun t => relabelEdge f g (a t)) (fun t => relabelEdge g f (b t)) =
      wordWeight a b := by
  classical
  unfold wordWeight
  rw [strictLeast_relabel_iff f g a]
  by_cases ha : StrictLeast a
  · simp only [if_pos ha]
    apply Finset.sum_congr rfl
    intro k _
    have h := strictLeast_relabel_iff g f (rotate k b)
    change (if StrictLeast (fun t => relabelEdge g f (b (t+k))) then -(k.val : ℤ) else 0) = _
    simpa only [rotate] using congrArg (fun p : Prop => if p then -(k.val : ℤ) else 0)
      (propext h)
  · simp only [if_neg ha]

abbrev Entry (n m : ℕ) := (Fin n × Fin m) ⊕ (Fin m × Fin n)

abbrev VertexWord (n m d : ℕ) := (Fin d → Fin n) × (Fin d → Fin m)

def Occurrence {n m d : ℕ} [NeZero d] (w : VertexWord n m d) : Entry n m → Type
  | Sum.inl ij => {t : Fin d // (w.1 t, w.2 t) = ij}
  | Sum.inr ji => {t : Fin d // (w.2 t, w.1 (t+1)) = ji}

instance occurrenceFintype {n m d : ℕ} [NeZero d] (w : VertexWord n m d)
    (e : Entry n m) : Fintype (Occurrence w e) := by
  classical
  cases e <;> dsimp [Occurrence] <;> infer_instance

abbrev WordType {n m d : ℕ} [NeZero d] (w : VertexWord n m d) :=
  ∀ e : Entry n m, Pattern (Occurrence w e)

abbrev Labels {n m d : ℕ} [NeZero d] (w : VertexWord n m d) (z : Entry n m → ℕ) :=
  ∀ e : Entry n m, Occurrence w e → Fin (z e)

abbrev WordRealization {n m d : ℕ} [NeZero d] {w : VertexWord n m d}
    (T : WordType w) (z : Entry n m → ℕ) :=
  ∀ e : Entry n m, Realization (T e) (z e)

def widths {n m d : ℕ} [NeZero d] {w : VertexWord n m d}
    (T : WordType w) : Entry n m → ℕ := fun e => (T e).1.val

def rankLabels {n m d : ℕ} [NeZero d] {w : VertexWord n m d}
    (T : WordType w) : Labels w (widths T) := fun e => (T e).2.val

def realizeLabels {n m d : ℕ} [NeZero d] {w : VertexWord n m d}
    {z : Entry n m → ℕ} (T : WordType w) (u : WordRealization T z) : Labels w z :=
  fun e a => (u e).val ((T e).2.val a)

/-- Distribute the per-entry decomposition over the actual occurrence fibers. -/
def wordRealizationEquiv {n m d : ℕ} [NeZero d] (w : VertexWord n m d)
    (z : Entry n m → ℕ) :
    (Σ T : WordType w, WordRealization T z) ≃ Labels w z :=
  (show (Σ T : WordType w, WordRealization T z) ≃
      (∀ e : Entry n m, Σ T : Pattern (Occurrence w e), Realization T (z e)) from
    { toFun := fun p e => ⟨p.1 e, p.2 e⟩
      invFun := fun q => ⟨fun e => (q e).1, fun e => (q e).2⟩
      left_inv := by rintro ⟨T,u⟩; rfl
      right_inv := by intro q; funext e; exact Sigma.eta (q e) }).trans
    (Equiv.piCongrRight fun e => realizationEquiv (Occurrence w e) (z e))

theorem wordRealization_card {n m d : ℕ} [NeZero d] {w : VertexWord n m d}
    (T : WordType w) (z : Entry n m → ℕ) :
    Fintype.card (WordRealization T z) = ∏ e : Entry n m, Nat.choose (z e) (widths T e) := by
  classical
  simp only [WordRealization, Fintype.card_pi, realization_card, widths]

def rMatrix {n m : ℕ} (z : Entry n m → ℕ) : CountMat n m :=
  fun i j => z (Sum.inl (i,j))

def sMatrix {n m : ℕ} (z : Entry n m → ℕ) : CountMat m n :=
  fun j i => z (Sum.inr (j,i))

def sourceEdge {n m d : ℕ} [NeZero d] (w : VertexWord n m d)
    (z : Entry n m → ℕ) (l : Labels w z) (t : Fin d) : Edge (rMatrix z * sMatrix z) :=
  join (rMatrix z) (sMatrix z)
    ⟨w.1 t, w.2 t, l (Sum.inl (w.1 t,w.2 t)) ⟨t,rfl⟩⟩
    ⟨w.2 t, w.1 (t+1), l (Sum.inr (w.2 t,w.1 (t+1))) ⟨t,rfl⟩⟩ rfl

/-- The actual forward rule (r_t,s_t) ↦ (s_t,r_(t+1)). -/
def targetEdge {n m d : ℕ} [NeZero d] (w : VertexWord n m d)
    (z : Entry n m → ℕ) (l : Labels w z) (t : Fin d) : Edge (sMatrix z * rMatrix z) :=
  join (sMatrix z) (rMatrix z)
    ⟨w.2 t, w.1 (t+1), l (Sum.inr (w.2 t,w.1 (t+1))) ⟨t,rfl⟩⟩
    ⟨w.1 (t+1), w.2 (t+1), l (Sum.inl (w.1 (t+1),w.2 (t+1))) ⟨t+1,rfl⟩⟩ rfl

theorem sourceEdge_legal {n m d : ℕ} [NeZero d] (w : VertexWord n m d)
    (z : Entry n m → ℕ) (l : Labels w z) (t : Fin d) :
    (sourceEdge w z l t).target = (sourceEdge w z l (t+1)).source := rfl

theorem targetEdge_legal {n m d : ℕ} [NeZero d] (w : VertexWord n m d)
    (z : Entry n m → ℕ) (l : Labels w z) (t : Fin d) :
    (targetEdge w z l t).target = (targetEdge w z l (t+1)).source := rfl

def rEmbedding {n m d : ℕ} [NeZero d] {w : VertexWord n m d}
    {z : Entry n m → ℕ} {T : WordType w} (u : WordRealization T z) :
    EntryEmbedding (rMatrix (widths T)) (rMatrix z) :=
  fun i j => OrderEmbedding.ofStrictMono (u (Sum.inl (i,j))).val (u (Sum.inl (i,j))).property

def sEmbedding {n m d : ℕ} [NeZero d] {w : VertexWord n m d}
    {z : Entry n m → ℕ} {T : WordType w} (u : WordRealization T z) :
    EntryEmbedding (sMatrix (widths T)) (sMatrix z) :=
  fun j i => OrderEmbedding.ofStrictMono (u (Sum.inr (j,i))).val (u (Sum.inr (j,i))).property

theorem sourceEdge_realize {n m d : ℕ} [NeZero d] {w : VertexWord n m d}
    {z : Entry n m → ℕ} (T : WordType w) (u : WordRealization T z) (t : Fin d) :
    sourceEdge w z (realizeLabels T u) t =
      relabelEdge (rEmbedding u) (sEmbedding u)
        (sourceEdge w (widths T) (rankLabels T) t) := by
  symm
  exact relabelEdge_join (rEmbedding u) (sEmbedding u) _ _ _ _ _

theorem targetEdge_realize {n m d : ℕ} [NeZero d] {w : VertexWord n m d}
    {z : Entry n m → ℕ} (T : WordType w) (u : WordRealization T z) (t : Fin d) :
    targetEdge w z (realizeLabels T u) t =
      relabelEdge (sEmbedding u) (rEmbedding u)
        (targetEdge w (widths T) (rankLabels T) t) := by
  symm
  exact relabelEdge_join (sEmbedding u) (rEmbedding u) _ _ _ _ _

/-- Lex least and primitive predicates are evaluated on ORIGINAL numbered
product edges. The common-order hypotheses used in comparing labels come
from equality of source, target, then intermediate vertex in relabelEdge_lt_iff. -/
theorem realized_wordWeight {n m d : ℕ} [NeZero d] {w : VertexWord n m d}
    {z : Entry n m → ℕ} (T : WordType w) (u : WordRealization T z) :
    wordWeight (sourceEdge w z (realizeLabels T u)) (targetEdge w z (realizeLabels T u)) =
      wordWeight (sourceEdge w (widths T) (rankLabels T))
        (targetEdge w (widths T) (rankLabels T)) := by
  have ha := funext (sourceEdge_realize T u)
  have hb := funext (targetEdge_realize T u)
  rw [ha, hb]
  exact wordWeight_relabel (rEmbedding u) (sEmbedding u) _ _

/-- This is a weighted finite sum on actual legal cyclic numbered words.
It is not yet named the relative gyration on periodic path orbits. -/
theorem numbered_word_sum_eq_order_types {n m d : ℕ} [NeZero d]
    (w : VertexWord n m d) (z : Entry n m → ℕ) :
    (∑ l : Labels w z, wordWeight (sourceEdge w z l) (targetEdge w z l)) =
      ∑ T : WordType w,
        wordWeight (sourceEdge w (widths T) (rankLabels T))
          (targetEdge w (widths T) (rankLabels T)) *
        (∏ e : Entry n m, Nat.choose (z e) (widths T e) : ℕ) := by
  classical
  let W := fun l : Labels w z => wordWeight (sourceEdge w z l) (targetEdge w z l)
  calc
    (∑ l : Labels w z, W l) =
        ∑ p : (Σ T : WordType w, WordRealization T z),
          W ((wordRealizationEquiv w z) p) :=
      ((wordRealizationEquiv w z).sum_comp W).symm
    _ = ∑ T : WordType w, ∑ u : WordRealization T z, W (realizeLabels T u) :=
      Fintype.sum_sigma _
    _ = ∑ T : WordType w,
        wordWeight (sourceEdge w (widths T) (rankLabels T))
          (targetEdge w (widths T) (rankLabels T)) *
        (∏ e : Entry n m, Nat.choose (z e) (widths T e) : ℕ) := by
      apply Finset.sum_congr rfl
      intro T _
      change (∑ u : WordRealization T z,
        wordWeight (sourceEdge w z (realizeLabels T u))
          (targetEdge w z (realizeLabels T u))) = _
      simp_rw [realized_wordWeight T]
      rw [Finset.sum_const, Finset.card_univ, wordRealization_card, nsmul_eq_mul]
      exact mul_comm _ _

/-! Signed-time periodic extension uses the existing block-address supplier.
All edge coordinates remain CountedMatrixOverlap.Edge coordinates. -/

open D5.S3.ConceptDynamics.Coding.FixedBlockRigidity.BlockCoordinates

def countedGraph {n : ℕ} (A : CountMat n n) :
    D5.S3.ConceptDynamics.Coding.EssentialWordRealization.DirectedMultigraph (Fin n) (Edge A) :=
  ⟨Edge.source, Edge.target⟩

def timeIndex {d : ℕ} [NeZero d] (t : ℤ) : Fin d :=
  (blockAddress (Nat.pos_of_ne_zero (NeZero.ne d)) t).2

theorem timeIndex_nat {d : ℕ} [NeZero d] (t : Fin d) : timeIndex (t.val : ℤ) = t := by
  have h := address_assemble (Nat.pos_of_ne_zero (NeZero.ne d)) ((0 : ℤ),t)
  have h' := congrArg Prod.snd h
  simpa only [assemble, zero_mul, zero_add, timeIndex] using h'

theorem timeIndex_add {d : ℕ} [NeZero d] (t : ℤ) (k : Fin d) :
    timeIndex (t+(k.val : ℤ)) = timeIndex t + k := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  change (((t+(k.val : ℤ)) % (d : ℤ)).toNat : ℤ) =
    ((((t % (d : ℤ)).toNat + k.val) % d : ℕ) : ℤ)
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne d)),
    Int.natCast_mod, Int.natCast_add,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne d))]
  rw [Int.add_emod]
  rw [Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ k.val) (by exact_mod_cast k.isLt)]

theorem timeIndex_succ {d : ℕ} [NeZero d] (t : ℤ) :
    timeIndex (d := d) (t+1) = timeIndex (d := d) t + 1 := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  change (((t+1) % (d : ℤ)).toNat : ℤ) =
    ((((t % (d : ℤ)).toNat + 1 % d) % d : ℕ) : ℤ)
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne d)),
    Int.natCast_mod, Int.natCast_add, Int.natCast_mod, Int.natCast_one,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne d))]
  exact Int.add_emod _ _ _

theorem timeIndex_period {d : ℕ} [NeZero d] (t : ℤ) :
    timeIndex (t+(d : ℤ)) = (timeIndex t : Fin d) := by
  apply Fin.ext
  change ((t+(d : ℤ)) % (d : ℤ)).toNat = (t % (d : ℤ)).toNat
  simp

def cyclicPath {n d : ℕ} [NeZero d] {A : CountMat n n}
    (a : Fin d → Edge A) (ha : ∀ t, (a t).target = (a (t+1)).source) : Path A :=
  ⟨fun t => a (timeIndex t), by
    intro t
    change (a (timeIndex t)).target = (a (timeIndex (t+1))).source
    rw [timeIndex_succ]
    exact ha _⟩

theorem cyclicPath_at {n d : ℕ} [NeZero d] {A : CountMat n n}
    (a : Fin d → Edge A) (ha : ∀ t, (a t).target = (a (t+1)).source) (t : Fin d) :
    (cyclicPath a ha).val (t.val : ℤ) = a t := by
  change a (timeIndex (t.val : ℤ)) = a t
  rw [timeIndex_nat]

theorem cyclicPath_eq_iff {n d : ℕ} [NeZero d] {A : CountMat n n}
    (a b : Fin d → Edge A)
    (ha : ∀ t, (a t).target = (a (t+1)).source)
    (hb : ∀ t, (b t).target = (b (t+1)).source) :
    cyclicPath a ha = cyclicPath b hb ↔ a = b := by
  constructor
  · intro h
    funext t
    have he := congrArg (fun x : Path A => x.val (t.val : ℤ)) h
    simpa only [cyclicPath_at] using he
  · intro h
    subst b
    rfl

theorem cyclicPath_period {n d : ℕ} [NeZero d] {A : CountMat n n}
    (a : Fin d → Edge A) (ha : ∀ t, (a t).target = (a (t+1)).source) :
    Function.IsPeriodicPt (shift A) d (cyclicPath a ha) := by
  change (shift A)^[d] (cyclicPath a ha) = cyclicPath a ha
  rw [show (shift A)^[d] (cyclicPath a ha) =
      translate (countedGraph A) (d : ℤ) (cyclicPath a ha) from
    shift_iterate_translate (countedGraph A) d (cyclicPath a ha)]
  apply Subtype.ext
  funext t
  change a (timeIndex (t+(d : ℤ))) = a (timeIndex t)
  rw [timeIndex_period]

theorem rotate_legal {n d : ℕ} [NeZero d] {A : CountMat n n}
    (a : Fin d → Edge A) (ha : ∀ t, (a t).target = (a (t+1)).source) (k : Fin d) :
    ∀ t, (rotate k a t).target = (rotate k a (t+1)).source := by
  intro t
  simpa only [rotate, add_assoc, add_comm k (1 : Fin d)] using ha (t+k)

theorem cyclicPath_rotate {n d : ℕ} [NeZero d] {A : CountMat n n}
    (a : Fin d → Edge A) (ha : ∀ t, (a t).target = (a (t+1)).source) (k : Fin d) :
    cyclicPath (rotate k a) (rotate_legal a ha k) = (shift A)^[k.val] (cyclicPath a ha) := by
  rw [show (shift A)^[k.val] (cyclicPath a ha) =
      translate (countedGraph A) (k.val : ℤ) (cyclicPath a ha) from
    shift_iterate_translate (countedGraph A) k.val (cyclicPath a ha)]
  apply Subtype.ext
  funext t
  change a (timeIndex t+k) = a (timeIndex (t+(k.val : ℤ)))
  rw [timeIndex_add]

/-- Finite-word primitivity is the actual minimal period of its signed-time
numbered path, not merely primitivity of vertex names. -/
theorem cyclicPath_minimalPeriod_iff {n d : ℕ} [NeZero d] {A : CountMat n n}
    (a : Fin d → Edge A) (ha : ∀ t, (a t).target = (a (t+1)).source) :
    Function.minimalPeriod (shift A) (cyclicPath a ha) = d ↔ Primitive a := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hper := cyclicPath_period a ha
  have hp : ∀ k : Fin d,
      Function.IsPeriodicPt (shift A) k.val (cyclicPath a ha) ↔ rotate k a = a := by
    intro k
    change (shift A)^[k.val] (cyclicPath a ha) = cyclicPath a ha ↔ _
    rw [← cyclicPath_rotate a ha k]
    exact cyclicPath_eq_iff _ _ _ _
  constructor
  · intro hm k hk hrot
    have hkp : 0 < k.val := by
      have hne : k.val ≠ 0 := by intro h; apply hk; exact Fin.ext h
      exact Nat.pos_of_ne_zero hne
    have hle := ((hp k).mpr hrot).minimalPeriod_le hkp
    rw [hm] at hle
    exact (Nat.not_le_of_lt k.isLt) hle
  · intro hprim
    have hle := hper.minimalPeriod_le hd
    apply Nat.le_antisymm hle
    by_contra hnot
    have hlt : Function.minimalPeriod (shift A) (cyclicPath a ha) < d := Nat.lt_of_not_ge hnot
    let k : Fin d := ⟨Function.minimalPeriod (shift A) (cyclicPath a ha), hlt⟩
    have hk : k ≠ 0 := by
      intro he
      have hz : k.val = 0 := congrArg Fin.val he
      exact (Nat.ne_of_gt (hper.minimalPeriod_pos hd)) hz
    exact hprim k hk ((hp k).mp (Function.isPeriodicPt_minimalPeriod _ _))

/-- The finite target word, periodically extended at ALL integer times, is
exactly the pinned elementaryHomeomorph of the finite source extension. -/
theorem elementary_source_cyclicPath {n m d : ℕ} [NeZero d]
    (w : VertexWord n m d) (z : Entry n m → ℕ) (l : Labels w z) :
    elementaryHomeomorph (rMatrix z) (sMatrix z)
        (cyclicPath (sourceEdge w z l) (sourceEdge_legal w z l)) =
      cyclicPath (targetEdge w z l) (targetEdge_legal w z l) := by
  apply Subtype.ext
  funext t
  rw [elementary_coordinate]
  change join _ _ (split _ _ (sourceEdge w z l (timeIndex t))).2
    (split _ _ (sourceEdge w z l (timeIndex (t+1)))).1 _ =
      targetEdge w z l (timeIndex t)
  have join_congr (a a' : Edge (sMatrix z)) (b b' : Edge (rMatrix z))
      (h : a.target = b.source) (h' : a'.target = b'.source)
      (ha : a = a') (hb : b = b') :
      join (sMatrix z) (rMatrix z) a b h =
        join (sMatrix z) (rMatrix z) a' b' h' := by
    subst a'
    subst b'
    rfl
  unfold targetEdge
  apply join_congr
  · simp only [sourceEdge, split_join]
  · simpa only [sourceEdge, split_join] using
      congrArg (fun q => (split (rMatrix z) (sMatrix z) (sourceEdge w z l q)).1)
        (timeIndex_succ (d := d) t)

end D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
