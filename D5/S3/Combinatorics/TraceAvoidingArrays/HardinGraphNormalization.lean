/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.normal_iff
   digest: Literal first-appearance normalization and the free signs of independent pair classes. -/

/-
admission_basis: escape-witness
normal_iff: proof_shape=content; consumer=fiberEquiv
fiberEquiv: proof_shape=content; consumer=fiber_card
first_before: proof_shape=bind-only; consumers=normal_iff, first_card
beta_small: proof_shape=bind-only; consumer=fiberEquiv
beta_lift: proof_shape=bind-only; consumer=fiberEquiv
lift_sign: proof_shape=bind-only; consumer=fiberEquiv
sign_lift: proof_shape=bind-only; consumer=fiberEquiv
first_card: proof_shape=content; consumer=fiber_card
fiber_card: proof_shape=content; consumer=result
graphFiberEquiv: proof_shape=bind-only; consumer=result
result: proof_shape=content; exact graph-normalization fiber count
escape_witness: normal_iff and the mutually inverse fiberEquiv construction
Audit source: Reg/D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.
Typed family proofs do not assert completed raw source-selection evidence; see issue #30456.
nextClass_spec: proof_shape=bind-only; consumers=canonical_kernel, canonical_ordered
canonical_kernel: proof_shape=bind-only; consumers=toPartition_surjective
canonical_ordered: proof_shape=content; consumers=toPartition_surjective
canonical_of_ordered: proof_shape=content; consumer=toPartition_injective
canonical_congr: proof_shape=bind-only; consumer=toPartition_injective
toPartition_injective: proof_shape=content; consumer=partitionEquiv
toPartition_surjective: proof_shape=content; consumer=partitionEquiv
partitionEquiv: proof_shape=content; consumer=literalPartitionEquiv
literalPartitionEquiv: proof_shape=content; terminal reversible partition/sign correspondence
paletteFiberEquiv: proof_shape=content; consumer=paletteColoringEquiv
paletteColoringEquiv: proof_shape=content; terminal reversible palette/class correspondence
The constructors and their inverse laws are statements about all positive graph sizes.
binary_ext: proof_shape=content; consumer=binaryColoringEquiv
binaryColoringEquiv: proof_shape=content; consumer=connected_count
stableFintype: proof_shape=bind-only; consumers=literal_card, palette_card
quotient_range_card: proof_shape=bind-only; consumer=literal_card
literal_card: proof_shape=bind-only; consumer=total_identity
palette_card: proof_shape=bind-only; consumer=total_identity
class_bounds: proof_shape=bind-only; consumer=total_identity
total_identity: proof_shape=bind-only; consumer=connected_count
connected_count: proof_shape=content; consumers=HardinThinGraphTransport.normalized_result, HardinThinGraphTransport.path_result
The numerical sum helpers are consumed by the connected theorem and its actual strips.
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.Combinatorics.Graph.Coloring.IndependentPartitionExpansion
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-! Literal scanner normalization and exact sign fibers for ordered graph colourings. -/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

/-- The literal source convention, including the first cell. -/
def Normal {n : ℕ} (f : Fin (n + 1) → Fin 6) : Prop :=
  f 0 = 0 ∧ HardinA233175PairStrip.good (false, false) f

/-- A first occurrence in the actual vertex order. -/
def First {n : ℕ} (p : Fin n → Fin 3) (i : Fin n) : Prop :=
  ∀ j, j < i → p j ≠ p i

instance {n : ℕ} (p : Fin n → Fin 3) (i : Fin n) : Decidable (First p i) :=
  inferInstanceAs (Decidable (∀ j, j < i → p j ≠ p i))

/-- The three class names occur in first-appearance order. -/
def Ordered {n : ℕ} (p : Fin (n + 1) → Fin 3) : Prop :=
  p 0 = 0 ∧ ∀ i, p i = 2 → ∃ j, j < i ∧ p j = 1

private theorem first_before {n : ℕ} (p : Fin n → Fin 3) (i : Fin n) :
    ∃ j, j ≤ i ∧ p j = p i ∧ First p j := by
  let s := Finset.univ.filter (fun j => p j = p i)
  have hi : i ∈ s := by simp [s]
  let j := s.min' ⟨i, hi⟩
  have hj : j ∈ s := Finset.min'_mem _ _
  refine ⟨j, Finset.min'_le _ _ hi, (Finset.mem_filter.mp hj).2, ?_⟩
  intro k hk he
  have hki : p k = p i := he.trans (Finset.mem_filter.mp hj).2
  have : j ≤ k := Finset.min'_le _ _ (by simp [s, hki])
  exact (not_le_of_gt hk) this

private theorem beta_small (c : Fin 3) : beta ⟨c.val, by omega⟩ = c := by
  fin_cases c <;> decide

/-- The scanner is exactly the ordered pair classes with their first signs fixed. -/
theorem normal_iff {n : ℕ} (f : Fin (n + 1) → Fin 6) :
    Normal f ↔ Ordered (beta ∘ f) ∧
      ∀ i, First (beta ∘ f) i → (f i).val = (beta (f i)).val := by
  simp only [Normal, HardinA233175PairStrip.good_iff, Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨h0, hn⟩
    refine ⟨⟨by simp [Function.comp_def, h0, beta], ?_⟩, ?_⟩
    · intro i hi
      have hc : f i = 2 ∨ f i = 3 := by
        change beta (f i) = 2 at hi
        generalize f i = c at hi ⊢
        fin_cases c <;> simp_all [beta]
      obtain ⟨j, hj, hjc⟩ := (hn i).1 (hc.elim Or.inl (fun h => Or.inr (Or.inl h)))
      exact ⟨j, hj, by simp [hjc, beta]⟩
    · intro i hf
      have h1 := (hn i).1
      have h2 := (hn i).2
      have hb0 : i ≠ 0 → beta (f i) ≠ 0 := by
        intro hi he
        exact hf 0 (Fin.pos_iff_ne_zero.mpr hi) (by simpa [Function.comp_def, h0, beta] using he.symm)
      generalize hc : f i = c at h1 h2 hb0 ⊢
      fin_cases c <;> norm_num [beta] at *
      · obtain ⟨j, hj, hcj⟩ := h2
        exact False.elim (hf j hj (by simp [hcj, hc]))
      · obtain ⟨j, hj, hcj⟩ := h1
        exact False.elim (hf j hj (by simp [hcj, hc]))
      · by_cases hi : i = 0
        · subst i; simp_all
        · exact False.elim (hi hb0)
  · rintro ⟨⟨h0, ho⟩, hf⟩
    have representative : ∀ i, ∃ j, j ≤ i ∧ f j = ⟨(beta (f i)).val, by omega⟩ := by
      intro i
      obtain ⟨j, hj, hp, hfirst⟩ := first_before (beta ∘ f) i
      refine ⟨j, hj, Fin.ext ?_⟩
      exact (hf j hfirst).trans (congrArg Fin.val hp)
    refine ⟨?_, ?_⟩
    · have hfirst : First (beta ∘ f) 0 := by intro j hj; exact False.elim ((by simp : ¬ j < 0) hj)
      apply Fin.ext
      exact (hf 0 hfirst).trans (congrArg Fin.val h0)
    · intro i
      constructor
      · intro hc
        have earlier1 : beta (f i) = 2 → ∃ j, j < i ∧ f j = 1 := by
          intro hi
          obtain ⟨j, hj, hp⟩ := ho i hi
          obtain ⟨k, hk, hkc⟩ := representative j
          exact ⟨k, lt_of_le_of_lt hk hj, by
            apply Fin.ext
            have hp' : beta (f j) = 1 := hp
            simpa [hp'] using congrArg Fin.val hkc⟩
        rcases hc with hc | hc | hc
        · apply earlier1; simp [hc, beta]
        · apply earlier1; simp [hc, beta]
        · obtain ⟨j, hj, hjc⟩ := representative i
          refine ⟨j, lt_of_le_of_ne hj ?_, ?_⟩
          · intro he; subst j; simp [hc, beta] at hjc
          · simpa [hc, beta] using hjc
      · intro hc
        obtain ⟨j, hj, hjc⟩ := representative i
        refine ⟨j, lt_of_le_of_ne hj ?_, ?_⟩
        · intro he; subst j; simp [hc, beta] at hjc
        · simpa [hc, beta] using hjc

/-- Choose a sign in a complementary pair. -/
def lift (p : Fin 3) (b : Bool) : Fin 6 :=
  if b then ⟨5 - p.val, by omega⟩ else ⟨p.val, by omega⟩

private theorem beta_lift (p : Fin 3) (b : Bool) : beta (lift p b) = p := by
  fin_cases p <;> cases b <;> decide

private theorem lift_sign (c : Fin 6) : lift (beta c) (decide (3 ≤ c.val)) = c := by
  fin_cases c <;> decide

private theorem sign_lift (p : Fin 3) (b : Bool) : decide (3 ≤ (lift p b).val) = b := by
  fin_cases p <;> cases b <;> decide

/-- Only nonminimal vertices carry free signs. -/
abbrev Free {n : ℕ} (p : Fin n → Fin 3) := {i // ¬ First p i}

/-- Literal lifts over a fixed ordered proper pair colouring. -/
def Fiber {n : ℕ} (p : Fin (n + 1) → Fin 3) :=
  {f : Fin (n + 1) → Fin 6 // Normal f ∧ beta ∘ f = p}

/-- Both inverse identities retain every actual colour assignment exactly once. -/
noncomputable def fiberEquiv {n : ℕ} (p : Fin (n + 1) → Fin 3) (hp : Ordered p) :
    Fiber p ≃ (Free p → Bool) where
  toFun f i := decide (3 ≤ (f.val i.val).val)
  invFun b := ⟨fun i => lift (p i) (if h : First p i then false else b ⟨i, h⟩), by
    have he : beta ∘ (fun i => lift (p i) (if h : First p i then false else b ⟨i, h⟩)) = p := by
      funext i; exact beta_lift _ _
    refine ⟨(normal_iff _).mpr ⟨by simpa only [he] using hp, ?_⟩, he⟩
    intro i hi
    have hip : First p i := by simpa only [he] using hi
    simp only [dite_eq_left hip, lift, Bool.false_eq_true, ↓reduceIte]
    exact (congrArg Fin.val (beta_small (p i))).symm⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    have he : beta (f.val i) = p i := congrFun f.property.2 i
    by_cases hi : First p i
    · have hfirst : First (beta ∘ f.val) i := by simpa only [f.property.2] using hi
      have hv := (normal_iff _).mp f.property.1 |>.2 i hfirst
      simp only [dite_eq_left hi, lift, Bool.false_eq_true, ↓reduceIte]
      apply Fin.ext
      exact (congrArg Fin.val he).symm.trans hv.symm
    · simp only [dite_eq_right hi]
      rw [← he]
      exact lift_sign _
  right_inv b := by
    funext i
    simp only [dite_eq_right i.property]
    exact sign_lift _ _

private theorem first_card {n : ℕ} (p : Fin n → Fin 3) :
    Fintype.card {i // First p i} = Fintype.card (Set.range p) := by
  classical
  let e : {i // First p i} → Set.range p := fun i => ⟨p i, ⟨i, rfl⟩⟩
  apply Fintype.card_of_bijective (f := e)
  constructor
  · intro i j h
    have hp : p i.val = p j.val := congrArg Subtype.val h
    apply Subtype.ext
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · exact False.elim (j.property i.val hij hp)
    · exact hij
    · exact False.elim (i.property j.val hij hp.symm)
  · rintro ⟨c, i, rfl⟩
    obtain ⟨j, _, hj, hf⟩ := first_before p i
    exact ⟨⟨j, hf⟩, Subtype.ext hj⟩

/-- Exact fibers, with one forced sign for each nonempty class. -/
private theorem fiber_card {n : ℕ} (p : Fin (n + 1) → Fin 3) (hp : Ordered p) :
    Nat.card (Fiber p) = 2 ^ (n + 1 - Fintype.card (Set.range p)) := by
  rw [Nat.card_congr (fiberEquiv p hp), Nat.card_eq_fintype_card]
  simp only [Fintype.card_fun, Fintype.card_bool, Free,
    Fintype.card_subtype_compl, Fintype.card_fin, first_card]

/-- Actual graph assignments, with the source bond condition. -/
def Legal {n : ℕ} (G : SimpleGraph (Fin (n + 1))) :=
  {f : Fin (n + 1) → Fin 6 // Normal f ∧
    ∀ i j, G.Adj i j → f i ≠ f j ∧ (f i).val + (f j).val ≠ 5}

/-- The graph fiber remembers the actual proper colouring, including unused labels. -/
def GraphFiber {n : ℕ} (G : SimpleGraph (Fin (n + 1))) (p : G.Coloring (Fin 3)) :=
  {f : Legal G // beta ∘ f.val = (p : Fin (n + 1) → Fin 3)}

private noncomputable def graphFiberEquiv {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (p : G.Coloring (Fin 3)) : GraphFiber G p ≃ Fiber (p : Fin (n + 1) → Fin 3) where
  toFun f := ⟨f.val.val, f.val.property.1, f.property⟩
  invFun f := ⟨⟨f.val, f.property.1, by
    intro i j hij
    apply (HardinA233251TriangleStrip.colour_bond_iff _ _).mpr
    have he := f.property.2
    simpa only [← congrFun he i, ← congrFun he j, Function.comp_apply] using p.valid hij⟩,
    f.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every ordered proper pair colouring has exactly 2^(N-j) literal graph lifts. -/
theorem result {n : ℕ} (G : SimpleGraph (Fin (n + 1))) (p : G.Coloring (Fin 3))
    (hp : Ordered (p : Fin (n + 1) → Fin 3)) :
    Nat.card (GraphFiber G p) =
      2 ^ (n + 1 - Fintype.card (Set.range (p : Fin (n + 1) → Fin 3))) := by
  rw [Nat.card_congr (graphFiberEquiv G p)]
  exact fiber_card _ hp

/-- The first vertex outside the initial class, or zero if there is none. -/
private noncomputable def nextClass {n : ℕ} (p : Fin (n + 1) → Fin 3) : Fin (n + 1) :=
  if h : ∃ i, p i ≠ p 0 then
    (Finset.univ.filter (fun i => p i ≠ p 0)).min' (by
      obtain ⟨i, hi⟩ := h
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩)
  else 0

private theorem nextClass_spec {n : ℕ} (p : Fin (n + 1) → Fin 3)
    (h : ∃ i, p i ≠ p 0) :
    p (nextClass p) ≠ p 0 ∧ ∀ i, p i ≠ p 0 → nextClass p ≤ i := by
  classical
  simp only [nextClass, dite_eq_left h]
  constructor
  · exact (Finset.mem_filter.mp (Finset.min'_mem
      (Finset.univ.filter (fun i => p i ≠ p 0)) _)).2
  · intro i hi
    exact Finset.min'_le _ _ (by simp [hi])

/-- Relabel the actual classes by their first vertices. -/
private noncomputable def canonical {n : ℕ} (p : Fin (n + 1) → Fin 3)
    (i : Fin (n + 1)) : Fin 3 :=
  if p i = p 0 then 0 else if p i = p (nextClass p) then 1 else 2

private theorem canonical_kernel {n : ℕ} (p : Fin (n + 1) → Fin 3) (i j) :
    canonical p i = canonical p j ↔ p i = p j := by
  classical
  by_cases h : ∃ k, p k ≠ p 0
  · have hab := (nextClass_spec p h).1
    unfold canonical
    generalize p i = a, p j = b, p 0 = c, p (nextClass p) = d at *
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp_all
  · have hp : ∀ k, p k = p 0 := by simpa using h
    simp [canonical, hp]

private theorem canonical_ordered {n : ℕ} (p : Fin (n + 1) → Fin 3) :
    Ordered (canonical p) := by
  classical
  refine ⟨by simp [canonical], ?_⟩
  intro i hi
  have hia : p i ≠ p 0 := by intro h; simp [canonical, h] at hi
  have h : ∃ k, p k ≠ p 0 := ⟨i, hia⟩
  have hs := nextClass_spec p h
  have hib : i ≠ nextClass p := by intro he; subst i; simp [canonical, hs.1] at hi
  exact ⟨nextClass p, lt_of_le_of_ne (hs.2 i hia) (Ne.symm hib), by simp [canonical, hs.1]⟩

private theorem canonical_of_ordered {n : ℕ} (p : Fin (n + 1) → Fin 3)
    (hp : Ordered p) : canonical p = p := by
  classical
  by_cases h : ∃ i, p i ≠ p 0
  · have hs := nextClass_spec p h
    have hb : p (nextClass p) = 1 := by
      have hn : p (nextClass p) ≠ 0 := by simpa [hp.1] using hs.1
      by_contra hh
      have htwo : p (nextClass p) = 2 := by omega
      obtain ⟨j, hj, hjp⟩ := hp.2 _ htwo
      have hle := hs.2 j (by simp [hjp, hp.1])
      exact (not_le_of_gt hj) hle
    funext i
    simp only [canonical, hp.1, hb]
    generalize p i = c
    fin_cases c <;> decide
  · have hc : ∀ i, p i = 0 := by simpa [hp.1] using h
    funext i
    simp [canonical, hc]

private theorem canonical_congr {n : ℕ} (p q : Fin (n + 1) → Fin 3)
    (h : ∀ i j, p i = p j ↔ q i = q j) : canonical p = canonical q := by
  classical
  have hn : nextClass p = nextClass q := by
    have he : (fun i => p i ≠ p 0) = (fun i => q i ≠ q 0) := by
      funext i; exact propext (not_congr (h i 0))
    unfold nextClass
    simp only [he]
  funext i
  simp only [canonical, hn, h i 0, h i (nextClass q)]

/-- An unlabelled partition into at most three nonempty independent sets.
The equivalence relation, rather than palette names, is the actual object. -/
structure StablePartition {n : ℕ} (G : SimpleGraph (Fin (n + 1))) where
  relation : Setoid (Fin (n + 1))
  independent : ∀ i j, G.Adj i j → ¬ relation.r i j
  atMostThree : Nat.card relation.classes ≤ 3

/-- Proper colourings whose labels are in first-appearance order. -/
abbrev OrderedColoring {n : ℕ} (G : SimpleGraph (Fin (n + 1))) :=
  {p : G.Coloring (Fin 3) // Ordered (p : Fin (n + 1) → Fin 3)}

private noncomputable def toPartition {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (p : OrderedColoring G) : StablePartition G := by
  classical
  letI := Fintype.ofFinite p.val.colorClasses
  exact ⟨Setoid.ker (p.val : Fin (n + 1) → Fin 3),
    fun _ _ h => p.val.valid h,
    by
      change Nat.card p.val.colorClasses ≤ 3
      rw [Nat.card_eq_fintype_card]
      exact p.val.card_colorClasses_le.trans (by simp)⟩

private theorem toPartition_injective {n : ℕ} (G : SimpleGraph (Fin (n + 1))) :
    Function.Injective (toPartition G) := by
  intro p q h
  have hr := congrArg StablePartition.relation h
  have he : ∀ i j, p.val i = p.val j ↔ q.val i = q.val j := by
    intro i j; exact Setoid.ext_iff.mp hr i j
  have hc := canonical_congr (p.val : Fin (n + 1) → Fin 3) q.val he
  rw [canonical_of_ordered _ p.property, canonical_of_ordered _ q.property] at hc
  apply Subtype.ext
  exact DFunLike.ext _ _ (congrFun hc)

private theorem toPartition_surjective {n : ℕ} (G : SimpleGraph (Fin (n + 1))) :
    Function.Surjective (toPartition G) := by
  classical
  intro S
  letI := Fintype.ofFinite (Quotient S.relation)
  have hcard : Fintype.card (Quotient S.relation) ≤ Fintype.card (Fin 3) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card,
      Nat.card_congr (Setoid.quotientEquivClasses S.relation)]
    exact S.atMostThree
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let p : G.Coloring (Fin 3) := SimpleGraph.Coloring.mk
    (fun i => e (Quotient.mk S.relation i)) (by
      intro i j hij he
      exact S.independent i j hij (Quotient.exact (e.injective he)))
  let q : G.Coloring (Fin 3) := SimpleGraph.Coloring.mk (canonical (p : Fin (n + 1) → Fin 3))
    (by intro i j hij he; exact p.valid hij ((canonical_kernel _ _ _).mp he))
  refine ⟨⟨q, canonical_ordered _⟩, ?_⟩
  have hr : (toPartition G ⟨q, canonical_ordered _⟩).relation = S.relation := by
    apply Setoid.ext
    intro i j
    change canonical (p : Fin (n + 1) → Fin 3) i = canonical (p : Fin (n + 1) → Fin 3) j ↔ _
    rw [canonical_kernel]
    change e (Quotient.mk S.relation i) = e (Quotient.mk S.relation j) ↔ _
    rw [e.injective.eq_iff, Quotient.eq]
  have hExt : ∀ A B : StablePartition G, A.relation = B.relation → A = B := by
    rintro ⟨a, ha, hc⟩ ⟨b, hb, hd⟩ he
    cases he
    rfl
  exact hExt _ _ hr

/-- Every unlabelled independent-set partition has exactly one ordered pair colouring. -/
noncomputable def partitionEquiv {n : ℕ} (G : SimpleGraph (Fin (n + 1))) :
    OrderedColoring G ≃ StablePartition G :=
  Equiv.ofBijective (toPartition G) ⟨toPartition_injective G, toPartition_surjective G⟩

/-- The actual proper pair colouring of a literal graph assignment. -/
private def pairColoring {n : ℕ} (G : SimpleGraph (Fin (n + 1))) (f : Legal G) :
    G.Coloring (Fin 3) :=
  SimpleGraph.Coloring.mk (beta ∘ f.val) (by
    intro i j hij
    exact (HardinA233251TriangleStrip.colour_bond_iff _ _).mp (f.property.2 i j hij))

/-- All literal assignments, with both inverses, indexed by unlabelled partitions and free signs. -/
noncomputable def literalPartitionEquiv {n : ℕ} (G : SimpleGraph (Fin (n + 1))) :
    Legal G ≃ Σ S : StablePartition G,
      (Free ((partitionEquiv G).symm S).val → Bool) := by
  classical
  let e : Legal G ≃ Σ p : OrderedColoring G, GraphFiber G p.val :=
    (Equiv.sigmaSubtypeFiberEquiv (pairColoring G)
      (fun p => Ordered (p : Fin (n + 1) → Fin 3))
      (fun f => (normal_iff f.val).mp f.property.1 |>.1)).symm.trans
      (Equiv.sigmaCongrRight fun p => Equiv.subtypeEquivRight fun f => by
        change pairColoring G f = p.val ↔ beta ∘ f.val = (p.val : Fin (n + 1) → Fin 3)
        constructor
        · intro h; exact congrArg (fun c : G.Coloring (Fin 3) => (c : Fin (n + 1) → Fin 3)) h
        · intro h; exact DFunLike.ext _ _ (congrFun h))
  exact e.trans ((Equiv.sigmaCongrRight fun p =>
    (graphFiberEquiv G p.val).trans (fiberEquiv _ p.property)).trans
      (Equiv.sigmaCongrLeft' (partitionEquiv G)))

/-- Proper palette colourings inducing one fixed unlabelled partition. -/
def PaletteFiber {n : ℕ} (G : SimpleGraph (Fin (n + 1))) (q : ℕ) (S : StablePartition G) :=
  {p : G.Coloring (Fin q) // Setoid.ker (p : Fin (n + 1) → Fin q) = S.relation}

/-- The palette names are exactly an injection from the actual nonempty classes. -/
noncomputable def paletteFiberEquiv {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (q : ℕ) (S : StablePartition G) :
    PaletteFiber G q S ≃ (Quotient S.relation ↪ Fin q) where
  toFun p :=
    { toFun := Quotient.lift (p.val : Fin (n + 1) → Fin q) (by
        intro i j h
        have he := p.property
        change (Setoid.ker (p.val : Fin (n + 1) → Fin q)).r i j
        rwa [he])
      inj' := by
        intro a b h
        induction a using Quotient.inductionOn with | h i =>
          induction b using Quotient.inductionOn with | h j =>
            apply Quotient.sound
            change S.relation.r i j
            rw [← p.property]
            exact h }
  invFun e := ⟨SimpleGraph.Coloring.mk (fun i => e (Quotient.mk S.relation i)) (by
    intro i j hij he
    exact S.independent i j hij (Quotient.exact (e.injective he))), by
      apply Setoid.ext
      intro i j
      change e (Quotient.mk S.relation i) = e (Quotient.mk S.relation j) ↔ _
      rw [e.injective.eq_iff, Quotient.eq]⟩
  left_inv p := by
    apply Subtype.ext
    exact DFunLike.ext _ _ (fun _ => rfl)
  right_inv e := by
    apply Function.Embedding.ext
    intro a
    induction a using Quotient.inductionOn with | h i => rfl
private noncomputable def palettePartition {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (q : ℕ) (hq : q ≤ 3) (p : G.Coloring (Fin q)) : StablePartition G := by
  classical
  letI := Fintype.ofFinite p.colorClasses
  refine ⟨Setoid.ker (p : Fin (n + 1) → Fin q), fun _ _ h => p.valid h, ?_⟩
  change Nat.card p.colorClasses ≤ 3
  rw [Nat.card_eq_fintype_card]
  exact p.card_colorClasses_le.trans (by simpa using hq)

/-- All proper colourings with at most three palette names are actual class injections. -/
noncomputable def paletteColoringEquiv {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (q : ℕ) (hq : q ≤ 3) : G.Coloring (Fin q) ≃
      Σ S : StablePartition G, (Quotient S.relation ↪ Fin q) := by
  classical
  refine (Equiv.sigmaFiberEquiv (palettePartition G q hq)).symm.trans ?_
  apply Equiv.sigmaCongrRight
  intro S
  refine (Equiv.subtypeEquivRight fun p => ?_).trans (paletteFiberEquiv G q S)
  change palettePartition G q hq p = S ↔ Setoid.ker (p : Fin (n + 1) → Fin q) = S.relation
  constructor
  · intro h; exact congrArg StablePartition.relation h
  · intro h
    have hExt : ∀ A B : StablePartition G, A.relation = B.relation → A = B := by
      rintro ⟨a, ha, hc⟩ ⟨b, hb, hd⟩ he
      cases he
      rfl
    exact hExt _ _ h


open scoped BigOperators

private theorem binary_ext {V : Type*} (G : SimpleGraph V) (hG : G.Preconnected)
    (r : V) (p q : G.Coloring (Fin 2)) (hr : p r = q r) : p = q := by
  apply DFunLike.ext
  intro v
  obtain ⟨w⟩ := hG r v
  have along {a b : V} (w : G.Walk a b) : p a = q a → p b = q b := by
    induction w with
    | nil => exact id
    | @cons a b c hab w ih =>
      intro he
      apply ih
      have hp := p.valid hab
      have hq := q.valid hab
      omega
  exact along w hr

/-- On a connected bipartite graph, the colour of one vertex determines the entire two-colouring. -/
noncomputable def binaryColoringEquiv {V : Type*} (G : SimpleGraph V)
    (hG : G.Preconnected) (r : V) (c : G.Coloring (Fin 2)) : G.Coloring (Fin 2) ≃ Fin 2 := by
  apply Equiv.ofBijective (fun p : G.Coloring (Fin 2) => p r)
  constructor
  · intro p q he; exact binary_ext G hG r p q he
  · intro b
    let e := Equiv.swap (c r) b
    let p : G.Coloring (Fin 2) := (SimpleGraph.Iso.completeGraph e).toHom.comp c
    refine ⟨p, ?_⟩
    exact Equiv.swap_apply_left (c r) b

private noncomputable instance stableFintype {n : ℕ}
    (G : SimpleGraph (Fin (n + 1))) : Fintype (StablePartition G) := by
  classical
  exact Fintype.ofEquiv (OrderedColoring G) (partitionEquiv G)

private theorem quotient_range_card {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (S : StablePartition G) :
    Nat.card (Quotient S.relation) =
      Fintype.card (Set.range (((partitionEquiv G).symm S).val : Fin (n + 1) → Fin 3)) := by
  let p := (partitionEquiv G).symm S
  have hs := congrArg StablePartition.relation ((partitionEquiv G).apply_symm_apply S)
  change Setoid.ker (p.val : Fin (n + 1) → Fin 3) = S.relation at hs
  rw [← hs, Nat.card_congr (Setoid.quotientKerEquivRange (p.val : Fin (n + 1) → Fin 3)),
    Nat.card_eq_fintype_card]

private theorem literal_card {n : ℕ} (G : SimpleGraph (Fin (n + 1))) :
    Nat.card (Legal G) =
      ∑ S : StablePartition G, 2 ^ (n + 1 - Nat.card (Quotient S.relation)) := by
  classical
  rw [Nat.card_congr (literalPartitionEquiv G), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro S _
  rw [quotient_range_card]
  exact (Nat.card_congr (fiberEquiv _ ((partitionEquiv G).symm S).property)).symm.trans
    (fiber_card _ ((partitionEquiv G).symm S).property)

private theorem palette_card {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (q : ℕ) (hq : q ≤ 3) :
    Nat.card (G.Coloring (Fin q)) =
      ∑ S : StablePartition G, q.descFactorial (Nat.card (Quotient S.relation)) := by
  classical
  rw [Nat.card_congr (paletteColoringEquiv G q hq), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro S _
  letI := Fintype.ofFinite (Quotient S.relation)
  simp only [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin]

private theorem class_bounds {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (S : StablePartition G) :
    1 ≤ Nat.card (Quotient S.relation) ∧ Nat.card (Quotient S.relation) ≤ 3 ∧
      Nat.card (Quotient S.relation) ≤ n + 1 := by
  have hpos : 0 < Nat.card (Quotient S.relation) := Nat.card_pos
  refine ⟨hpos, ?_, ?_⟩
  · rw [Nat.card_congr (Setoid.quotientEquivClasses S.relation)]
    exact S.atMostThree
  · simpa using Nat.card_le_card_of_surjective
      (Quotient.mk S.relation) (Quotient.mk_surjective)

private theorem total_identity {n : ℕ} (G : SimpleGraph (Fin (n + 1))) :
    48 * Nat.card (Legal G) = 2 ^ (n + 1) *
      (Nat.card (G.Coloring (Fin 3)) + 3 * Nat.card (G.Coloring (Fin 2)) +
        15 * Nat.card (G.Coloring (Fin 1))) := by
  classical
  rw [literal_card, palette_card G 3 (by decide), palette_card G 2 (by decide),
    palette_card G 1 (by decide)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  obtain ⟨hpos, hthree, hN⟩ := class_bounds G S
  generalize hj : Nat.card (Quotient S.relation) = j at *
  have he := Nat.sub_add_cancel hN
  have hp := congrArg (fun k : ℕ => 2 ^ k) he
  rw [pow_add] at hp
  interval_cases j <;> norm_num [Nat.descFactorial, pow_succ] at hp ⊢ <;> nlinarith


/-- The edge and connected bipartition give the exact small-palette terms.
The cross-multiplied identity includes two and three vertices without truncated exponents. -/
theorem connected_count {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (hG : G.Preconnected) (hc : G.Colorable 2)
    (he : ∃ u v, G.Adj u v) :
    Nat.card (G.Coloring (Fin 1)) = 0 ∧ Nat.card (G.Coloring (Fin 2)) = 2 ∧
      48 * Nat.card (Legal G) = 2 ^ (n + 1) * (Nat.card (G.Coloring (Fin 3)) + 6) := by
  have h1 : Nat.card (G.Coloring (Fin 1)) = 0 := by
    letI : IsEmpty (G.Coloring (Fin 1)) := ⟨by
      intro p
      obtain ⟨u,v,huv⟩ := he
      exact p.valid huv (Subsingleton.elim _ _)⟩
    exact Nat.card_of_isEmpty
  have h2 : Nat.card (G.Coloring (Fin 2)) = 2 := by
    rw [Nat.card_congr (binaryColoringEquiv G hG 0 hc.some)]
    simp
  refine ⟨h1,h2,?_⟩
  have ht := total_identity G
  rw [h1,h2] at ht
  norm_num at ht ⊢
  exact ht

namespace Complementary

open HardinA233177Canonical (Canonical canonical_exists_unique)
open D5.S3.Combinatorics.Graph.Coloring

/-- The complementary colour in the literal palette. -/
def complement {p : ℕ} (c : Fin (2 * p)) : Fin (2 * p) :=
  ⟨2 * p - 1 - c.val, by have := c.isLt; omega⟩

/-- The lower member of a complementary pair is its label. -/
def pair {p : ℕ} (c : Fin (2 * p)) : Fin p :=
  ⟨min c.val (complement c).val, by
    have := c.isLt
    change min c.val (2 * p - 1 - c.val) < p
    omega⟩

/-- The upper half of the palette carries sign true. -/
def sign {p : ℕ} (c : Fin (2 * p)) : Bool := decide (p ≤ c.val)

/-- Recover the actual colour from the pair label and sign. -/
def lift {p : ℕ} (t : Fin p) (b : Bool) : Fin (2 * p) :=
  if b then complement ⟨t.val, by have := t.isLt; omega⟩
  else ⟨t.val, by have := t.isLt; omega⟩

private theorem pair_low {p : ℕ} (c : Fin (2 * p)) (h : c.val < p) :
    (pair c).val = c.val := by
  change min c.val (2 * p - 1 - c.val) = c.val
  rw [min_eq_left (by omega)]

private theorem pair_high {p : ℕ} (c : Fin (2 * p)) (h : p ≤ c.val) :
    (pair c).val = 2 * p - 1 - c.val := by
  change min c.val (2 * p - 1 - c.val) = _
  rw [min_eq_right (by omega)]

/-- Literal palette coordinates, with the complementary lift as inverse. -/
def colourEquiv (p : ℕ) : Fin (2 * p) ≃ Fin p × Bool where
  toFun c := (pair c, sign c)
  invFun t := lift t.1 t.2
  left_inv c := by
    apply Fin.ext
    have hc := c.isLt
    by_cases h : p ≤ c.val
    · simpa [sign, h, lift, complement, pair_high c h] using
        (show 2 * p - 1 - (2 * p - 1 - c.val) = c.val by omega)
    · simp [sign, h, lift, pair_low c (by omega)]
  right_inv := by
    rintro ⟨t, b⟩
    have ht := t.isLt
    cases b
    · have h : (lift t false).val < p := ht
      apply Prod.ext
      · exact Fin.ext (pair_low _ h)
      · simp [sign, Nat.not_le.mpr h]
    · have h : p ≤ (lift t true).val := by
        change p ≤ 2 * p - 1 - t.val
        omega
      apply Prod.ext
      · apply Fin.ext
        rw [pair_high _ h]
        change 2 * p - 1 - (2 * p - 1 - t.val) = t.val
        omega
      · simp [sign, h]

private theorem pair_lift {p : ℕ} (t : Fin p) (b : Bool) : pair (lift t b) = t :=
  congrArg Prod.fst ((colourEquiv p).apply_symm_apply (t, b))

private theorem sign_lift {p : ℕ} (t : Fin p) (b : Bool) : sign (lift t b) = b :=
  congrArg Prod.snd ((colourEquiv p).apply_symm_apply (t, b))

private theorem lift_sign {p : ℕ} (c : Fin (2 * p)) : lift (pair c) (sign c) = c :=
  (colourEquiv p).symm_apply_apply c

/-- Unequal pair labels are exactly the source bond rule. -/
theorem bond_iff {p : ℕ} (c d : Fin (2 * p)) :
    pair c ≠ pair d ↔ c ≠ d ∧ c.val + d.val ≠ 2 * p - 1 := by
  have hc := c.isLt
  have hd := d.isLt
  simp only [ne_eq, Fin.ext_iff]
  by_cases h : c.val < p
  · rw [pair_low c h]
    by_cases k : d.val < p
    · rw [pair_low d k]; omega
    · rw [pair_high d (by omega)]; omega
  · rw [pair_high c (by omega)]
    by_cases k : d.val < p
    · rw [pair_low d k]; omega
    · rw [pair_high d (by omega)]; omega

variable {V : Type*} {p : ℕ}

/-- The least vertex of a nonempty label class. -/
def First [LT V] {K : Type*} (a : V → K) (i : V) : Prop :=
  ∀ j, j < i → a j ≠ a i

/-- The vertices at which either literal sign is allowed. -/
abbrev Free [LT V] {K : Type*} (a : V → K) := {i // ¬ First a i}

/-- The actual first-appearance convention for arbitrary pairs. -/
def Normal [LT V] (f : V → Fin (2 * p)) : Prop :=
  Canonical (pair ∘ f) ∧ ∀ i, First (pair ∘ f) i → sign (f i) = false

/-- Normalized literal assignments satisfying the literal bond on every edge. -/
def Legal [LT V] (G : SimpleGraph V) (p : ℕ) :=
  {f : V → Fin (2 * p) // Normal f ∧
    ∀ i j, G.Adj i j → f i ≠ f j ∧ (f i).val + (f j).val ≠ 2 * p - 1}

/-- The actual partitions into at most p nonempty independent blocks. -/
abbrev AtMost (G : SimpleGraph V) (p : ℕ) :=
  {P : G.Partition // Nat.card P.parts ≤ p}

/-- Proper pair words with first-appearance labels. -/
abbrev OrderedColoring [LT V] (G : SimpleGraph V) (p : ℕ) :=
  {a : G.Coloring (Fin p) // Canonical (a : V → Fin p)}

private noncomputable abbrev namesToWord {G : SimpleGraph V} (P : G.Partition) (e : P.parts ↪ Fin p) :
    V → Fin p := fun i => e (P.toColoring i)

private theorem parts_surjective {G : SimpleGraph V} (P : G.Partition) :
    Function.Surjective P.toColoring := by
  intro s
  obtain ⟨v, hv⟩ := Setoid.nonempty_of_mem_partition P.isPartition s.property
  refine ⟨v, Subtype.ext ?_⟩
  exact Setoid.eq_of_mem_eqv_class P.isPartition.2
    (P.partOfVertex_mem v) (P.mem_partOfVertex v) s.property hv

noncomputable section

variable [Fintype V] [LinearOrder V]

private theorem unique_names {G : SimpleGraph V} (P : AtMost G p) :
    ∃! e : P.val.parts ↪ Fin p, Canonical (namesToWord P.val e) := by
  classical
  letI := Fintype.ofFinite P.val.parts
  have hcard : Fintype.card P.val.parts ≤ Fintype.card (Fin p) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_fin] using P.property
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  obtain ⟨a, ⟨ha, σ, hσ⟩, huniq⟩ := canonical_exists_unique (namesToWord P.val e)
  let d := e.trans σ.toEmbedding
  have hd : namesToWord P.val d = a := hσ.symm
  refine ⟨d, ?_, ?_⟩
  · change Canonical (namesToWord P.val d)
    rw [hd]
    exact ha
  intro q hq
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair e q e.injective q.injective
  have he := huniq (namesToWord P.val q) ⟨hq, τ, funext fun i => (hτ _).symm⟩
  apply Function.Embedding.ext
  intro s
  obtain ⟨i, rfl⟩ := parts_surjective P.val s
  exact congrFun (he.trans hd.symm) i

private def namedPartitionEquiv (G : SimpleGraph V) (p : ℕ) :
    OrderedColoring G p ≃ Σ P : AtMost G p, {e : P.val.parts ↪ Fin p //
      Canonical (namesToWord P.val e)} := by
  classical
  let E := IndependentPartitionExpansion.coloringEquiv G (Fin p)
  refine (Equiv.subtypeEquiv (p := fun a : G.Coloring (Fin p) => Canonical (a : V → Fin p))
    (q := fun x : Σ P : G.Partition, P.parts ↪ Fin p =>
      Nat.card x.1.parts ≤ p ∧ Canonical (namesToWord x.1 x.2)) E ?_).trans
      (Equiv.subtypeSigmaEquivSigma (α := G.Partition) (β := fun P => P.parts ↪ Fin p)
        (p := fun P => Nat.card P.parts ≤ p) (q := fun P e => Canonical (namesToWord P e)))
  intro a
  have hcard : Nat.card (E a).1.parts ≤ p := by
    simpa using Nat.card_le_card_of_injective (E a).2 (E a).2.injective
  have hword : namesToWord (E a).1 (E a).2 = (a : V → Fin p) :=
    congrArg (fun c : G.Coloring (Fin p) => (c : V → Fin p)) (E.symm_apply_apply a)
  rw [hword]
  exact ⟨fun ha => ⟨hcard, ha⟩, And.right⟩

/-- Canonical pair words correspond to the actual unlabelled independent partitions. -/
def partitionEquiv (G : SimpleGraph V) (p : ℕ) : OrderedColoring G p ≃ AtMost G p := by
  classical
  letI (P : AtMost G p) : Unique {e : P.val.parts ↪ Fin p //
      Canonical (namesToWord P.val e)} :=
    ⟨⟨⟨(unique_names P).choose, (unique_names P).choose_spec.1⟩⟩,
      fun e => Subtype.ext ((unique_names P).choose_spec.2 e.val e.property)⟩
  exact (namedPartitionEquiv G p).trans (Equiv.sigmaUnique _ _)

/-- Read the canonical pair word from a normalized literal assignment. -/
def toOrderedColoring (G : SimpleGraph V) (f : Legal G p) : OrderedColoring G p :=
  ⟨SimpleGraph.Coloring.mk (pair ∘ f.val)
    (fun h => (bond_iff _ _).mpr (f.property.2 _ _ h)), f.property.1.1⟩

/-- For a fixed canonical proper word, restrict signs to non-first vertices and lift back. -/
def fiberEquiv {G : SimpleGraph V} (a : OrderedColoring G p) :
    {f : Legal G p // toOrderedColoring G f = a} ≃ (Free (a.val : V → Fin p) → Bool) := by
  classical
  let build (b : Free (a.val : V → Fin p) → Bool) (i : V) :=
    lift (a.val i) (if h : First (a.val : V → Fin p) i then false else b ⟨i, h⟩)
  have hpair (b) : pair ∘ build b = (a.val : V → Fin p) :=
    funext fun i => pair_lift (a.val i) _
  have hsign (b) (i : V) :
      sign (build b i) = if h : First (a.val : V → Fin p) i then false else b ⟨i, h⟩ :=
    sign_lift (a.val i) _
  refine ⟨fun f i => sign (f.val.val i.val), fun b => ⟨⟨build b, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · refine ⟨(hpair b).symm ▸ a.property, ?_⟩
    intro i hi
    rw [hpair b] at hi
    rw [hsign b, dite_eq_left hi]
  · intro i j hij
    apply (bond_iff _ _).mp
    change (pair ∘ build b) i ≠ (pair ∘ build b) j
    rw [hpair b]
    exact a.val.valid hij
  · apply Subtype.ext
    exact DFunLike.ext _ _ (congrFun (hpair b))
  · intro f
    have hword : pair ∘ f.val.val = (a.val : V → Fin p) :=
      congrArg (fun c : OrderedColoring G p => (c.val : V → Fin p)) f.property
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change build (fun j => sign (f.val.val j.val)) i = f.val.val i
    unfold build
    rw [← congrFun hword i]
    by_cases hi : First (a.val : V → Fin p) i
    · have hf : First (pair ∘ f.val.val) i := hword.symm ▸ hi
      rw [dite_eq_left hi, ← f.val.property.1.2 i hf]
      exact lift_sign _
    · rw [dite_eq_right hi]
      exact lift_sign _
  · intro b
    funext i
    change sign (build b i.val) = b i
    rw [hsign b, dite_eq_right i.property]

/-- Actual graph assignments decompose into their unlabelled independent blocks and free signs. -/
def literalPartitionEquiv (G : SimpleGraph V) (p : ℕ) :
    Legal G p ≃ Σ P : AtMost G p, (Free (((partitionEquiv G p).symm P).val : V → Fin p) → Bool) :=
  (Equiv.sigmaFiberEquiv (toOrderedColoring G)).symm.trans
    ((Equiv.sigmaCongrRight fiberEquiv).trans (Equiv.sigmaCongrLeft' (partitionEquiv G p)))

private theorem first_iff_part {G : SimpleGraph V} (P : G.Partition) (e : P.parts ↪ Fin p)
    (i : V) : First (namesToWord P e) i ↔ First (P.toColoring : V → P.parts) i := by
  simp only [First, namesToWord, e.injective.ne_iff]

private def firstBlockEquiv {G : SimpleGraph V} (P : G.Partition) :
    {i // First (P.toColoring : V → P.parts) i} ≃ P.parts :=
  Equiv.ofBijective (fun i => P.toColoring i.val) (by
    classical
    constructor
    · intro i j h
      apply Subtype.ext
      rcases lt_trichotomy i.val j.val with hij | hij | hij
      · exact False.elim (j.property i.val hij h)
      · exact hij
      · exact False.elim (i.property j.val hij h.symm)
    · intro s
      let t := Finset.univ.filter (fun i => P.toColoring i = s)
      obtain ⟨v, hv⟩ := parts_surjective P s
      let hne : t.Nonempty := ⟨v, by simp [t, hv]⟩
      let i := t.min' hne
      have hi : P.toColoring i = s :=
        (Finset.mem_filter.mp (Finset.min'_mem t hne)).2
      refine ⟨⟨i, ?_⟩, hi⟩
      intro j hlt hj
      exact (not_le_of_gt hlt) (Finset.min'_le t j (by simp [t, hj, hi])))

private theorem free_card_names {G : SimpleGraph V} (P : G.Partition) (e : P.parts ↪ Fin p) :
    Nat.card (Free (namesToWord P e)) = Fintype.card V - Nat.card P.parts := by
  classical
  letI := Fintype.ofFinite P.parts
  have hfirst : Fintype.card {i // First (namesToWord P e) i} = Fintype.card P.parts :=
    Fintype.card_congr ((Equiv.subtypeEquivRight (first_iff_part P e)).trans (firstBlockEquiv P))
  rw [Nat.card_eq_fintype_card]
  change Fintype.card {i // ¬ First (namesToWord P e) i} = _
  rw [Fintype.card_subtype_compl, hfirst, Nat.card_eq_fintype_card]

/-- The domain of the free signs has exactly one fewer vertex for each nonempty block. -/
theorem free_card (G : SimpleGraph V) (P : AtMost G p) :
    Nat.card (Free (((partitionEquiv G p).symm P).val : V → Fin p)) =
      Fintype.card V - Nat.card P.val.parts := by
  classical
  let a := (partitionEquiv G p).symm P
  let E := IndependentPartitionExpansion.coloringEquiv G (Fin p)
  have hname : namesToWord (E a.val).1 (E a.val).2 = (a.val : V → Fin p) :=
    congrArg (fun c : G.Coloring (Fin p) => (c : V → Fin p)) (E.symm_apply_apply a.val)
  have hpart : (E a.val).1 = P.val :=
    congrArg Subtype.val ((partitionEquiv G p).apply_symm_apply P)
  calc
    Nat.card (Free (a.val : V → Fin p)) = Nat.card (Free (namesToWord (E a.val).1 (E a.val).2)) :=
      congrArg (fun w : V → Fin p => Nat.card (Free w)) hname.symm
    _ = Fintype.card V - Nat.card ((E a.val).1.parts) := free_card_names _ _
    _ = Fintype.card V - Nat.card P.val.parts := by rw [hpart]

private theorem parts_bound (G : SimpleGraph V) [Nonempty V] (P : AtMost G p) :
    Nat.card P.val.parts ∈ Finset.Icc 1 (min p (Fintype.card V)) := by
  have hpos : Nonempty P.val.parts := Nonempty.map P.val.toColoring inferInstance
  have hN : Nat.card P.val.parts ≤ Fintype.card V := by
    simpa using Nat.card_le_card_of_surjective P.val.toColoring (parts_surjective P.val)
  exact Finset.mem_Icc.mpr ⟨Nat.card_pos, le_min P.property hN⟩

private def exactPartsEquiv (G : SimpleGraph V) (k : ℕ) (hk : k ≤ p) :
    {P : AtMost G p // Nat.card P.val.parts = k} ≃
      {P : G.Partition // Nat.card P.parts = k} where
  toFun P := ⟨P.val.val, P.property⟩
  invFun P := ⟨⟨P.val, P.property.symm ▸ hk⟩, P.property⟩

/-- The source count uses the actual literal assignments and the graphical Stirling numbers. -/
theorem card_eq_sum (G : SimpleGraph V) [Nonempty V] (p : ℕ) :
    Nat.card (Legal G p) =
      ∑ k ∈ Finset.Icc 1 (min p (Fintype.card V)),
        2 ^ (Fintype.card V - k) * IndependentPartitionExpansion.stirling G k := by
  classical
  have hsum : Nat.card (Legal G p) =
      ∑ P : AtMost G p, 2 ^ (Fintype.card V - Nat.card P.val.parts) := by
    rw [Nat.card_congr (literalPartitionEquiv G p), Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro P _
    rw [Nat.card_fun, free_card]
    simp
  rw [hsum, ← Finset.sum_fiberwise_of_maps_to'
    (f := fun k => 2 ^ (Fintype.card V - k))
    (g := fun P : AtMost G p => Nat.card P.val.parts)
    (t := Finset.Icc 1 (min p (Fintype.card V))) (by intro P _; exact parts_bound G P)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkp : k ≤ p := (Finset.mem_Icc.mp hk).2.trans (min_le_left _ _)
  have he := Nat.card_congr (exactPartsEquiv G k hkp)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at he
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm _ (2 ^ _),
    IndependentPartitionExpansion.stirling, he]

end

private theorem sign_false_iff {p : ℕ} (c : Fin (2 * p)) :
    sign c = false ↔ c.val = (pair c).val := by
  have hc := c.isLt
  by_cases h : c.val < p
  · simp [sign, Nat.not_le.mpr h, pair_low c h]
  · rw [pair_high c (by omega)]
    simp only [sign, show p ≤ c.val by omega, decide_true, Bool.true_eq_false, false_iff]
    omega

private theorem canonical_iff_ordered {n : ℕ} (a : Fin (n + 1) → Fin 3) :
    Canonical a ↔ HardinGraphNormalization.Ordered a := by
  constructor
  · intro h
    refine ⟨?_, fun i hi => h i 1 (by simp [hi])⟩
    by_contra hz
    have hlt : (0 : Fin 3) < a 0 := Fin.pos_iff_ne_zero.mpr hz
    obtain ⟨i, hi, _⟩ := h 0 0 hlt
    exact (by simp : ¬ i < 0) hi
  · rintro ⟨h0, h2⟩ i b hb
    have hb' : b = 0 ∨ b = 1 := by omega
    rcases hb' with rfl | rfl
    · refine ⟨0, Fin.pos_iff_ne_zero.mpr ?_, h0⟩
      intro hi
      subst i
      rw [h0] at hb
      exact (lt_irrefl _) hb
    · exact h2 i (by omega)

private theorem pair_three : (pair (p := 3)) = beta := by
  funext c
  fin_cases c <;> decide +kernel

/-- At three pairs the identity on literal words identifies the original scanner and bonds. -/
def scannerEquiv {n : ℕ} (G : SimpleGraph (Fin (n + 1))) :
    Legal G 3 ≃ HardinGraphNormalization.Legal G := by
  apply Equiv.subtypeEquivRight
  intro f
  have hn : Normal f ↔ HardinGraphNormalization.Normal f := by
    rw [HardinGraphNormalization.normal_iff, Normal, pair_three, canonical_iff_ordered]
    simp only [sign_false_iff, pair_three, First, HardinGraphNormalization.First]
  exact and_congr hn Iff.rfl

end Complementary

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization
