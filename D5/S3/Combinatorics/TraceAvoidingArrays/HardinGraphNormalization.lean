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
Typed family proofs do not assert completed raw source-selection evidence.
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Tactic

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
        exact hf 0 (Fin.pos_iff_ne_zero.mpr hi) (by simp [Function.comp_def, h0, beta] using he.symm)
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

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization
