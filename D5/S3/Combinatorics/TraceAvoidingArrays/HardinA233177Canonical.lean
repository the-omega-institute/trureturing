/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.finite_certificate
   digest: First-appearance representatives and exact complementary-pair colour fibres. -/
/-
admission_basis: open-problem-resolution (#28449; Proved)
escape_witness: canonical_unique (well-founded prefix rigidity),
  canonical_exists_unique (lex-minimal relabelling gives a canonical representative).
direct_frozen_dependencies (raw compiled type/value edges, union over this module):
  D5/S3/Observer/Separation/BooleanRankThreeK4.beta
    statement_id: sha256:1abdc5f3db71567fe05de5aabbe80dddeb5ec5179e4ec7fd49fe71e500518481
Canonical: proof_shape=bind-only; consumers=canonical_exists_unique, normalized_card
first_occurrence: proof_shape=bind-only; consumers=canonical_exists_unique, firstEquiv
canonical_unique: proof_shape=content; consumers=canonical_exists_unique, canonical_pattern_card
  reason: Well-founded induction proves rigidity from equality of label fibres.
canonical_exists_unique: proof_shape=content; consumers=canonical_pattern_card
  reason: A label swap proves the lex-minimal orbit member canonical; rigidity gives uniqueness.
colourEquiv: proof_shape=bind-only; consumers=fibreEquiv
Normal: proof_shape=bind-only; consumers=normalization_iff, normalized_card
FirstSides: proof_shape=bind-only; consumers=normalization_iff, Fibre
normalization_iff: proof_shape=bind-only; consumers=normalized_card
First: proof_shape=bind-only; consumers=firstEquiv, fibreEquiv
firstEquiv: proof_shape=bind-only; consumers=fibre_card
Fibre: proof_shape=bind-only; consumers=fibre_card, normalized_card
side_false: proof_shape=bind-only; consumers=fibreEquiv
fibreEquiv: proof_shape=bind-only; consumers=fibre_card
fibre_card: proof_shape=bind-only; consumers=normalized_card
perm_ext_two: proof_shape=bind-only; consumers=canonical_pattern_card
canonical_pattern_card: proof_shape=content; consumers=HardinA233177Ladder.counting_bridge
  reason: The counting bijection uses the new canonical representative and its rigidity.
normalized_card: proof_shape=bind-only; consumers=HardinA233177Ladder.counting_bridge
-/
import Mathlib.Order.PiLex
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic
import D5.S3.Observer.Separation.BooleanRankThreeK4

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

def Canonical {C : Type*} [LT C] {k : ℕ} (P : C → Fin k) : Prop :=
  ∀ i b, b < P i → ∃ j, j < i ∧ P j = b

private theorem first_occurrence {C : Type*} [Fintype C] [LinearOrder C]
    {K : Type*} [DecidableEq K] (P : C → K) (i : C) :
    ∃ j, j ≤ i ∧ P j = P i ∧ ∀ t, t < j → P t ≠ P j := by
  classical
  let s := Finset.univ.filter (fun j => P j = P i)
  have hi : i ∈ s := by simp [s]
  let j := s.min' ⟨i, hi⟩
  have hj : j ∈ s := Finset.min'_mem _ _
  have he : P j = P i := (Finset.mem_filter.mp hj).2
  refine ⟨j, Finset.min'_le s i hi, he, ?_⟩
  intro t ht h
  have hm : t ∈ s := by simp [s, h, he]
  exact (not_le_of_gt ht) (Finset.min'_le s t hm)

private theorem canonical_unique {C : Type*} [Fintype C] [LinearOrder C]
    {k : ℕ} (P Q : C → Fin k) (hP : Canonical P) (hQ : Canonical Q)
    (h : ∀ i j, P i = P j ↔ Q i = Q j) : P = Q := by
  funext i
  induction i using (wellFounded_lt (α := C)).induction with
  | h i ih =>
    apply le_antisymm
    · by_contra hn
      obtain ⟨j, hj, he⟩ := hP i (Q i) (lt_of_not_ge hn)
      have hp : P j = P i := (h j i).mpr (by rw [← ih j hj, he])
      exact (ne_of_lt (lt_of_not_ge hn)) (he.symm.trans hp)
    · by_contra hn
      obtain ⟨j, hj, he⟩ := hQ i (P i) (lt_of_not_ge hn)
      have hq : Q j = Q i := (h j i).mp (by rw [ih j hj, he])
      exact (ne_of_lt (lt_of_not_ge hn)) (he.symm.trans hq)

theorem canonical_exists_unique {C : Type*} [Fintype C] [LinearOrder C]
    {k : ℕ} (P : C → Fin k) :
    ∃! Q : C → Fin k, Canonical Q ∧ ∃ e : Equiv.Perm (Fin k), Q = e ∘ P := by
  classical
  let orbit : Finset (Lex (C → Fin k)) :=
    Finset.univ.image (fun e : Equiv.Perm (Fin k) => toLex (e ∘ P))
  have ho : orbit.Nonempty := ⟨toLex P, by
    apply Finset.mem_image.mpr
    exact ⟨Equiv.refl _, Finset.mem_univ _, rfl⟩⟩
  let Q : C → Fin k := ofLex (orbit.min' ho)
  have hQmem : toLex Q ∈ orbit := Finset.min'_mem orbit ho
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp hQmem
  have hQe : Q = e ∘ P := by simpa only [toLex_inj] using he.symm
  have hQ : Canonical Q := by
    intro i b hb
    by_contra hn
    obtain ⟨j, hji, hjiQ, hj⟩ := first_occurrence Q i
    let τ := Equiv.swap b (Q i)
    have hsmall : toLex (τ ∘ Q) < toLex Q := by
      refine ⟨j, ?_, ?_⟩
      · intro t ht
        change τ (Q t) = Q t
        apply Equiv.swap_apply_of_ne_of_ne
        · intro heq
          exact hn ⟨t, lt_of_lt_of_le ht hji, heq⟩
        · simpa only [hjiQ] using hj t ht
      · change τ (Q j) < Q j
        simpa [τ, hjiQ] using hb
    have hm : toLex (τ ∘ Q) ∈ orbit := by
      apply Finset.mem_image.mpr
      refine ⟨e.trans τ, Finset.mem_univ _, ?_⟩
      simp only [hQe, Function.comp_assoc, Equiv.coe_trans]
    exact (not_lt_of_ge (Finset.min'_le orbit _ hm)) hsmall
  refine ⟨Q, ⟨hQ, e, hQe⟩, ?_⟩
  rintro R ⟨hR, d, rfl⟩
  apply canonical_unique _ _ hR hQ
  intro i j
  simp only [Function.comp_apply, hQe, d.injective.eq_iff, e.injective.eq_iff]

open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

private def colourEquiv : Fin 6 ≃ Fin 3 × Bool where
  toFun x := (beta x, decide (3 ≤ x.val))
  invFun p := if p.2 then ⟨5 - p.1.val, by have := p.1.isLt; omega⟩
    else ⟨p.1.val, by have := p.1.isLt; omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def Normal {C : Type*} [LT C] (f : C → Fin 6) : Prop :=
  ∀ i,
    ((f i = 2 ∨ f i = 3 ∨ f i = 4) → ∃ j, j < i ∧ f j = 1) ∧
    (f i = 3 → ∃ j, j < i ∧ f j = 2)

def FirstSides {C : Type*} [LT C] (f : C → Fin 6) : Prop :=
  ∀ i, (∀ j, j < i → beta (f j) ≠ beta (f i)) → (f i).val = (beta (f i)).val

theorem normalization_iff {C : Type*} [Fintype C] [LinearOrder C]
    (z : C) (hz : ∀ i, z ≤ i) (f : C → Fin 6) (hf : f z = 0) :
    Normal f ↔ Canonical (beta ∘ f) ∧ FirstSides f := by
  classical
  have h0 : beta (0 : Fin 6) = 0 := rfl
  constructor
  · intro hn
    have before (i : C) (hi : beta (f i) ≠ 0) : z < i := by
      apply lt_of_le_of_ne (hz i)
      intro he
      subst i
      exact hi (by rw [hf, h0])
    constructor
    · intro i b hb
      change b < beta (f i) at hb
      by_cases hb0 : b = 0
      · subst b
        refine ⟨z, before i (ne_of_gt hb), ?_⟩
        change beta (f z) = 0
        rw [hf, h0]
      · have hx : ∀ x : Fin 6, ∀ b : Fin 3, b ≠ 0 → b < beta x →
            b = 1 ∧ (x = 2 ∨ x = 3) := by decide +kernel
        obtain ⟨rfl, hx⟩ := hx (f i) b hb0 hb
        obtain ⟨j, hj, he⟩ := (hn i).1 (hx.elim Or.inl (fun h => Or.inr (Or.inl h)))
        exact ⟨j, hj, by change beta (f j) = 1; rw [he]; rfl⟩
    · intro i hi
      have hi' := hn i
      generalize he : f i = x at *
      fin_cases x
      · rfl
      · rfl
      · rfl
      · obtain ⟨j, hj, h⟩ := hi'.2 rfl
        exact False.elim (hi j hj (by rw [h]; rfl))
      · obtain ⟨j, hj, h⟩ := hi'.1 (Or.inr (Or.inr rfl))
        exact False.elim (hi j hj (by rw [h]; rfl))
      · have hzlt : z < i := by
          apply lt_of_le_of_ne (hz i)
          intro hei
          have hv := congrArg (fun j => (f j).val) hei
          rw [hf, he] at hv
          norm_num at hv
        exact False.elim (hi z hzlt (by rw [hf]; rfl))
  · rintro ⟨hc, hs⟩
    have lift (i : C) (d : Fin 3) (h : ∃ j, j < i ∧ beta (f j) = d) :
        ∃ j, j < i ∧ (f j).val = d.val := by
      obtain ⟨j, hj, hd⟩ := h
      obtain ⟨t, ht, he, hfirst⟩ := first_occurrence (beta ∘ f) j
      have hs' := hs t hfirst
      refine ⟨t, lt_of_le_of_lt ht hj, ?_⟩
      exact hs'.trans (congrArg Fin.val (he.trans hd))
    have earlier (i : C) (h : (f i).val ≠ (beta (f i)).val) :
        ∃ j, j < i ∧ beta (f j) = beta (f i) := by
      by_contra hn
      apply h
      apply hs i
      intro j hj he
      exact hn ⟨j, hj, he⟩
    intro i
    constructor
    · intro h
      have hlabel : ∃ j, j < i ∧ beta (f j) = 1 := by
        rcases h with h | h | h
        · exact hc i 1 (by change (1 : Fin 3) < beta (f i); rw [h]; decide)
        · exact hc i 1 (by change (1 : Fin 3) < beta (f i); rw [h]; decide)
        · have he := earlier i (by rw [h]; decide)
          simpa only [h, show beta (4 : Fin 6) = 1 from rfl] using he
      obtain ⟨j, hj, he⟩ := lift i 1 hlabel
      exact ⟨j, hj, Fin.ext he⟩
    · intro h
      have he := earlier i (by rw [h]; decide)
      have hlabel : ∃ j, j < i ∧ beta (f j) = 2 := by
        simpa only [h, show beta (3 : Fin 6) = 2 from rfl] using he
      obtain ⟨j, hj, he⟩ := lift i 2 hlabel
      exact ⟨j, hj, Fin.ext he⟩

private abbrev First {C : Type*} [LT C] {K : Type*} (P : C → K) (i : C) : Prop :=
  ∀ j, j < i → P j ≠ P i

private noncomputable def firstEquiv {C : Type*} [Fintype C] [LinearOrder C]
    {K : Type*} [DecidableEq K] (P : C → K) :
    {i // First P i} ≃ Set.range P :=
  Equiv.ofBijective (fun i => ⟨P i.val, i.val, rfl⟩) (by
    constructor
    · intro i j he
      have h : P i.val = P j.val := congrArg Subtype.val he
      apply Subtype.ext
      rcases lt_trichotomy i.val j.val with hlt | heq | hgt
      · exact False.elim (j.property i.val hlt h)
      · exact heq
      · exact False.elim (i.property j.val hgt h.symm)
    · rintro ⟨b, i, rfl⟩
      obtain ⟨j, _, hj, hfirst⟩ := first_occurrence P i
      exact ⟨⟨j, hfirst⟩, Subtype.ext hj⟩)

abbrev Fibre {C : Type*} [LT C] (P : C → Fin 3) :=
  {f : C → Fin 6 // (∀ i, beta (f i) = P i) ∧ FirstSides f}

private theorem side_false (x : Fin 6) :
    (colourEquiv x).2 = false ↔ x.val = (beta x).val := by
  fin_cases x <;> decide +kernel

private noncomputable def fibreEquiv {C : Type*} [Fintype C] [LinearOrder C]
    (P : C → Fin 3) : Fibre P ≃ ({i // ¬ First P i} → Bool) := by
  classical
  let build (b : {i // ¬ First P i} → Bool) (i : C) : Fin 6 :=
    colourEquiv.symm (P i, if hi : First P i then false else b ⟨i, hi⟩)
  have build_label (b : {i // ¬ First P i} → Bool) (i : C) :
      beta (build b i) = P i := by
    exact congrArg Prod.fst (colourEquiv.apply_symm_apply _)
  have build_bit (b : {i // ¬ First P i} → Bool) (i : C) :
      (colourEquiv (build b i)).2 = if hi : First P i then false else b ⟨i, hi⟩ := by
    exact congrArg Prod.snd (colourEquiv.apply_symm_apply _)
  refine {
    toFun := fun f i => (colourEquiv (f.val i.val)).2
    invFun := fun b => ⟨build b, build_label b, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro i hi
    apply (side_false _).mp
    rw [build_bit]
    have hf : First P i := by
      intro j hj he
      exact hi j hj (by rw [build_label, build_label, he])
    simp only [dite_eq_left hf]
  · intro f
    apply Subtype.ext
    funext i
    change build (fun j => (colourEquiv (f.val j.val)).2) i = f.val i
    apply colourEquiv.injective
    apply Prod.ext
    · change beta (build (fun j => (colourEquiv (f.val j.val)).2) i) = beta (f.val i)
      exact (build_label (fun j => (colourEquiv (f.val j.val)).2) i).trans
        (f.property.1 i).symm
    · rw [build_bit (fun j => (colourEquiv (f.val j.val)).2) i]
      by_cases hi : First P i
      · rw [dite_eq_left hi]
        apply ((side_false _).mpr (f.property.2 i ?_)).symm
        intro j hj he
        exact hi j hj (by rw [← f.property.1 j, ← f.property.1 i]; exact he)
      · rw [dite_eq_right hi]
  · intro b
    funext i
    change (colourEquiv (build b i.val)).2 = b i
    rw [build_bit, dite_eq_right i.property]

theorem fibre_card {C : Type*} [Fintype C] [LinearOrder C] (P : C → Fin 3) :
    Nat.card (Fibre P) = 2 ^ (Fintype.card C - Nat.card (Set.range P)) := by
  classical
  have hf : Fintype.card {i // First P i} = Fintype.card (Set.range P) :=
    Fintype.card_congr (firstEquiv P)
  rw [Nat.card_congr (fibreEquiv P), Nat.card_eq_fintype_card]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl, hf,
    Nat.card_eq_fintype_card]

private theorem perm_ext_two : ∀ (e d : Equiv.Perm (Fin 3)) (a b : Fin 3),
    a ≠ b → e a = d a → e b = d b → e = d := by
  decide +kernel

theorem canonical_pattern_card {C : Type*} [Fintype C] [LinearOrder C]
    (S : (C → Fin 3) → Prop)
    (hinv : ∀ e : Equiv.Perm (Fin 3), ∀ P, S (e ∘ P) ↔ S P)
    (huse : ∀ P, S P → ∃ i j, P i ≠ P j) :
    Nat.card {P // S P} = 6 * Nat.card {P // S P ∧ Canonical P} := by
  classical
  let E : ({P // S P ∧ Canonical P} × Equiv.Perm (Fin 3)) → {P // S P} :=
    fun q => ⟨q.2 ∘ q.1.val, (hinv q.2 q.1.val).mpr q.1.property.1⟩
  have hE : Function.Bijective E := by
    constructor
    · rintro ⟨Q, e⟩ ⟨R, d⟩ he
      have heq : e ∘ Q.val = d ∘ R.val := congrArg Subtype.val he
      have hQR : Q.val = R.val := by
        apply canonical_unique _ _ Q.property.2 R.property.2
        intro i j
        calc
          Q.val i = Q.val j ↔ e (Q.val i) = e (Q.val j) := e.injective.eq_iff.symm
          _ ↔ d (R.val i) = d (R.val j) := by
            rw [show e (Q.val i) = d (R.val i) from congrFun heq i,
              show e (Q.val j) = d (R.val j) from congrFun heq j]
          _ ↔ R.val i = R.val j := d.injective.eq_iff
      have hsub : Q = R := Subtype.ext hQR
      subst R
      obtain ⟨i, j, hij⟩ := huse Q.val Q.property.1
      have hed : e = d := perm_ext_two e d (Q.val i) (Q.val j) hij
        (congrFun heq i) (congrFun heq j)
      exact Prod.ext rfl hed
    · intro P
      obtain ⟨Q, ⟨hQ, e, he⟩, _⟩ := canonical_exists_unique P.val
      have hSQ : S Q := he ▸ (hinv e P.val).mpr P.property
      refine ⟨(⟨Q, hSQ, hQ⟩, e.symm), ?_⟩
      apply Subtype.ext
      funext i
      change e.symm (Q i) = P.val i
      rw [he]
      exact e.symm_apply_apply _
  have hc := Nat.card_congr (Equiv.ofBijective E hE)
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 3)),
    Fintype.card_perm, Fintype.card_fin] at hc
  norm_num at hc
  simpa only [Nat.mul_comm, Nat.card_eq_fintype_card] using hc.symm

open scoped Classical in
theorem normalized_card {C : Type*} [Fintype C] [LinearOrder C]
    (z : C) (hz : ∀ i, z ≤ i) (S : (C → Fin 3) → Prop) :
    Nat.card {f : C → Fin 6 // S (beta ∘ f) ∧ f z = 0 ∧ Normal f} =
      ∑ P : {P : C → Fin 3 // S P ∧ Canonical P},
        2 ^ (Fintype.card C - Nat.card (Set.range P.val)) := by
  classical
  have first_zero (P : C → Fin 3) (hc : Canonical P) : P z = 0 := by
    by_contra hn
    have hlt : (0 : Fin 3) < P z := Fin.pos_iff_ne_zero.mpr hn
    obtain ⟨j, hj, _⟩ := hc z 0 hlt
    exact (not_lt_of_ge (hz j)) hj
  have mk_normal (P : {P : C → Fin 3 // S P ∧ Canonical P}) (f : Fibre P.val) :
      S (beta ∘ f.val) ∧ f.val z = 0 ∧ Normal f.val := by
    have heq : beta ∘ f.val = P.val := funext f.property.1
    have hc : Canonical (beta ∘ f.val) := by rw [heq]; exact P.property.2
    have hzero : f.val z = 0 := by
      have hfirst := f.property.2 z (fun j hj => False.elim ((not_lt_of_ge (hz j)) hj))
      apply Fin.ext
      exact hfirst.trans (congrArg Fin.val ((f.property.1 z).trans
        (first_zero P.val P.property.2)))
    exact ⟨by rw [heq]; exact P.property.1, hzero,
      (normalization_iff z hz f.val hzero).mpr ⟨hc, f.property.2⟩⟩
  let E : (Σ P : {P : C → Fin 3 // S P ∧ Canonical P}, Fibre P.val) →
      {f : C → Fin 6 // S (beta ∘ f) ∧ f z = 0 ∧ Normal f} :=
    fun p => ⟨p.2.val, mk_normal p.1 p.2⟩
  have hE : Function.Bijective E := by
    constructor
    · rintro ⟨P, f⟩ ⟨Q, g⟩ h
      have hfg : f.val = g.val := congrArg Subtype.val h
      have hPQ : P = Q := by
        apply Subtype.ext
        funext i
        rw [← f.property.1 i, ← g.property.1 i, hfg]
      cases hPQ
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext hfg))
    · intro f
      have hn := (normalization_iff z hz f.val f.property.2.1).mp f.property.2.2
      exact ⟨⟨⟨beta ∘ f.val, f.property.1, hn.1⟩, ⟨f.val, fun _ => rfl, hn.2⟩⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective E hE), Nat.card_eq_fintype_card,
    Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro P _
  simpa only [Nat.card_eq_fintype_card] using fibre_card P.val

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
