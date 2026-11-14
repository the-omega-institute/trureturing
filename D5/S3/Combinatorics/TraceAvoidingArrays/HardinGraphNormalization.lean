/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization
   mirror-E: none
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
They do not assert the subsequent numerical sums or strip transports.
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

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

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization
