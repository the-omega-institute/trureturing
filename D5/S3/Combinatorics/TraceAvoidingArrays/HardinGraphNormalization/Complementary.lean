/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal complementary colours, canonical independent partitions, and the exact free-sign count. -/

/-
admission_basis: escape-witness
escape_witness: the literal palette and partition-fibre inverses for every finite graph and
palette size, consumed by the weighted graphical Stirling identity.
bond_iff: proof_shape=content; consumers=toOrderedColoring, fiberEquiv
colourEquiv: proof_shape=content; consumer=fiberEquiv via pair_lift, sign_lift, lift_sign
partitionEquiv: proof_shape=content; consumer=literalPartitionEquiv
fiberEquiv: proof_shape=content; consumer=literalPartitionEquiv
literalPartitionEquiv: proof_shape=content; consumer=card_eq_sum
free_card: proof_shape=content; consumer=card_eq_sum
card_eq_sum: proof_shape=content; arbitrary-p literal count by actual partitions
scannerEquiv: proof_shape=content; identity on literal words at three pairs
The private palette, block and sum helpers are consumed in this correspondence and count.
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.Combinatorics.Graph.Coloring.IndependentPartitionExpansion

/-! Actual complementary-palette normalization and independent partition counts. -/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Complementary

open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)
open scoped BigOperators

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

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Complementary
