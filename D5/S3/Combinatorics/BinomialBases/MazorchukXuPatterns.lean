/- GID: D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/MazorchukXuPatterns
   mirror-E: none(waiver:universal-coordinate-refinement-arguments)
   anchors: [mathlib/module/Mathlib.Order.Prod.Lex.Basic]
   utility: none
   digest: Zero- and tie-preserving refinement of exceptional coordinate graphs. -/

import D5.S3.Combinatorics.BinomialBases.MazorchukXuGeneric
import Mathlib.Order.Prod.Lex.Basic

/-! Ordered coordinate graphs retain arbitrary exceptional edges and every coordinate tie. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MazorchukXu

/-- Ordinary ranks, including zero, and labelled exceptional vertices. The position list
is a type parameter so that each list carries its own vertex order. -/
inductive CoordinateVertex {i : ℕ} (p : Fin i → ℕ) where
  | ordinary : ℕ → CoordinateVertex p
  | exceptional : Fin i → CoordinateVertex p

/-- Ordinary rank r precedes all exceptions in position r; exception labels break ties. -/
def coordinateKey {i : ℕ} (p : Fin i → ℕ) : CoordinateVertex p → ℕ ×ₗ ℕ
  | .ordinary r => toLex (r, 0)
  | .exceptional j => toLex (p j, j.val + 1)

private theorem coordinateKey_injective {i : ℕ} (p : Fin i → ℕ) :
    Function.Injective (coordinateKey p) := by
  intro u v h
  cases u with
  | ordinary r =>
    cases v with
    | ordinary s => exact congrArg CoordinateVertex.ordinary (by simpa [coordinateKey] using h)
    | exceptional j =>
      have := congrArg (fun z : ℕ ×ₗ ℕ => (ofLex z).2) h
      simp only [coordinateKey, ofLex_toLex] at this
      omega
  | exceptional j =>
    cases v with
    | ordinary r =>
      have := congrArg (fun z : ℕ ×ₗ ℕ => (ofLex z).2) h
      simp only [coordinateKey, ofLex_toLex] at this
      omega
    | exceptional k =>
      have hh := congrArg (fun z : ℕ ×ₗ ℕ => (ofLex z).2) h
      simp only [coordinateKey, ofLex_toLex] at hh
      have : j = k := Fin.ext (by omega)
      exact congrArg CoordinateVertex.exceptional this

instance coordinateLinearOrder {i : ℕ} (p : Fin i → ℕ) : LinearOrder (CoordinateVertex p) :=
  LinearOrder.lift' (coordinateKey p) (coordinateKey_injective p)

/-- The coordinate graph: ordinary ranks form a clique, exception j is incident to
ordinary r precisely when c(j)<r, and exceptional edges are supplied by B. -/
def coordinateEdges {i : ℕ} (p c : Fin i → ℕ) (B : Fin i → Fin i → Prop)
    (u v : CoordinateVertex p) : Prop :=
  u < v ∧ match u, v with
    | .ordinary _, .ordinary _ => True
    | .ordinary r, .exceptional j => c j < r
    | .exceptional j, .ordinary r => c j < r
    | .exceptional j, .exceptional k => B j k

private theorem ordinary_lt_ordinary {i : ℕ} {p : Fin i → ℕ} (r s : ℕ) :
    (CoordinateVertex.ordinary r : CoordinateVertex p) < CoordinateVertex.ordinary s ↔ r < s := by
  change coordinateKey p (.ordinary r) < coordinateKey p (.ordinary s) ↔ _
  simp [coordinateKey, Prod.Lex.toLex_lt_toLex]

private theorem ordinary_lt_exceptional {i : ℕ} {p : Fin i → ℕ} (r : ℕ) (j : Fin i) :
    (CoordinateVertex.ordinary r : CoordinateVertex p) < CoordinateVertex.exceptional j ↔ r ≤ p j := by
  change coordinateKey p (.ordinary r) < coordinateKey p (.exceptional j) ↔ _
  simp only [coordinateKey, Prod.Lex.toLex_lt_toLex, Nat.lt_add_one, Nat.zero_le, and_true]
  omega

private theorem exceptional_lt_ordinary {i : ℕ} {p : Fin i → ℕ} (j : Fin i) (r : ℕ) :
    (CoordinateVertex.exceptional j : CoordinateVertex p) < CoordinateVertex.ordinary r ↔ p j < r := by
  change coordinateKey p (.exceptional j) < coordinateKey p (.ordinary r) ↔ _
  simp [coordinateKey, Prod.Lex.toLex_lt_toLex]

private theorem exceptional_lt_exceptional {i : ℕ} {p : Fin i → ℕ} (j k : Fin i) :
    (CoordinateVertex.exceptional j : CoordinateVertex p) < CoordinateVertex.exceptional k ↔
      p j < p k ∨ p j = p k ∧ j < k := by
  change coordinateKey p (.exceptional j) < coordinateKey p (.exceptional k) ↔ _
  simp [coordinateKey, Prod.Lex.toLex_lt_toLex]

private noncomputable def rankCeil (e : ℕ → ℕ) (he : StrictMono e) (r : ℕ) : ℕ :=
  Nat.find (show ∃ k, r ≤ e k from ⟨r, he.id_le r⟩)

private theorem rankCeil_le_iff (e : ℕ → ℕ) (he : StrictMono e) (r k : ℕ) :
    rankCeil e he r ≤ k ↔ r ≤ e k := by
  constructor
  · intro h
    exact (Nat.find_spec (show ∃ k, r ≤ e k from ⟨r, he.id_le r⟩)).trans (he.monotone h)
  · intro h
    exact Nat.find_min' _ h

private theorem rankCeil_embedding (e : ℕ → ℕ) (he : StrictMono e) (k : ℕ) :
    rankCeil e he (e k) = k := by
  apply le_antisymm
  · exact (rankCeil_le_iff e he _ _).mpr le_rfl
  · exact he.le_iff_le.mp ((rankCeil_le_iff e he _ _).mp le_rfl)

private theorem rankCeil_mono (e : ℕ → ℕ) (he : StrictMono e) :
    Monotone (rankCeil e he) := by
  intro r s hrs
  apply (rankCeil_le_iff e he _ _).mpr
  exact hrs.trans ((rankCeil_le_iff e he _ _).mp le_rfl)

private def coordinateCollapse {i : ℕ} (p : Fin i → ℕ) (f : ℕ → ℕ)
    (e : ℕ → ℕ) : CoordinateVertex (e ∘ p) → CoordinateVertex p
  | .ordinary r => .ordinary (f r)
  | .exceptional j => .exceptional j

private def coordinateSection {i : ℕ} (p : Fin i → ℕ) (e : ℕ → ℕ) :
    CoordinateVertex p → CoordinateVertex (e ∘ p)
  | .ordinary r => .ordinary (e r)
  | .exceptional j => .exceptional j

private theorem coordinateSection_strictMono {i : ℕ} (p : Fin i → ℕ)
    (e : ℕ → ℕ) (he : StrictMono e) : StrictMono (coordinateSection p e) := by
  intro u v huv
  cases u with
  | ordinary r =>
    cases v with
    | ordinary s => exact (ordinary_lt_ordinary _ _).mpr (he ((ordinary_lt_ordinary _ _).mp huv))
    | exceptional j =>
      exact (ordinary_lt_exceptional _ _).mpr
        (he.monotone ((ordinary_lt_exceptional _ _).mp huv))
  | exceptional j =>
    cases v with
    | ordinary r =>
      exact (exceptional_lt_ordinary _ _).mpr
        (he ((exceptional_lt_ordinary _ _).mp huv))
    | exceptional k =>
      simp only [coordinateSection, coordinateCollapse, exceptional_lt_exceptional,
        Function.comp_apply, he.lt_iff_lt, he.injective.eq_iff] at huv ⊢
      exact huv

private theorem coordinateCollapse_monotone {i : ℕ} (p : Fin i → ℕ)
    (e : ℕ → ℕ) (he : StrictMono e) :
    Monotone (coordinateCollapse p (rankCeil e he) e) := by
  apply monotone_iff_forall_lt.mpr
  intro u v huv
  cases u with
  | ordinary r =>
    cases v with
    | ordinary s =>
      have hrs := (ordinary_lt_ordinary _ _).mp huv
      exact le_of_lt_or_eq (by
        rcases lt_or_eq_of_le (rankCeil_mono e he hrs.le) with h | h
        · exact Or.inl ((ordinary_lt_ordinary _ _).mpr h)
        · exact Or.inr (congrArg CoordinateVertex.ordinary h))
    | exceptional j =>
      apply le_of_lt
      apply (ordinary_lt_exceptional _ _).mpr
      exact (rankCeil_le_iff e he _ _).mpr ((ordinary_lt_exceptional _ _).mp huv)
  | exceptional j =>
    cases v with
    | ordinary r =>
      apply le_of_lt
      apply (exceptional_lt_ordinary _ _).mpr
      have h := (exceptional_lt_ordinary _ _).mp huv
      have hc := (rankCeil_le_iff e he r (p j))
      change e (p j) < r at h
      omega
    | exceptional k =>
      apply le_of_lt
      simp only [coordinateSection, coordinateCollapse, exceptional_lt_exceptional,
        Function.comp_apply, he.lt_iff_lt, he.injective.eq_iff] at huv ⊢
      exact huv

/-- Simultaneously stretching positions and cutoffs by any increasing map fixing zero
preserves and reflects admissibility, with arbitrary ties and exceptional-edge bits. -/
theorem coordinate_rules_refinement_iff {i : ℕ} (p c : Fin i → ℕ)
    (B : Fin i → Fin i → Prop) (e : ℕ → ℕ) (he : StrictMono e) (_he0 : e 0 = 0) :
    Rules (coordinateEdges (e ∘ p) (e ∘ c) B) ↔ Rules (coordinateEdges p c B) := by
  let f := coordinateCollapse p (rankCeil e he) e
  let s := coordinateSection p e
  have hfs : ∀ u, f (s u) = u := by
    intro u
    cases u with
    | ordinary r => exact congrArg CoordinateVertex.ordinary (rankCeil_embedding e he r)
    | exceptional j => rfl
  have hgraph : coordinateEdges (e ∘ p) (e ∘ c) B =
      cliqueLift (coordinateEdges p c B) f := by
    funext u v
    apply propext
    cases u with
    | ordinary r =>
      cases v with
      | ordinary t =>
        simp only [coordinateEdges, cliqueLift, and_true]
        constructor
        · intro hrt
          refine ⟨hrt, ?_⟩
          have hf := coordinateCollapse_monotone p e he hrt.le
          rcases lt_or_eq_of_le hf with h | h
          · exact Or.inr ⟨h, trivial⟩
          · exact Or.inl h
        · exact And.left
      | exceptional j =>
        simp only [coordinateEdges, cliqueLift, coordinateCollapse, f, reduceCtorEq,
          false_or, ordinary_lt_exceptional, Function.comp_apply]
        rw [rankCeil_le_iff]
        have hcut : e (c j) < r ↔ c j < rankCeil e he r := by
          have := rankCeil_le_iff e he r (c j)
          omega
        rw [hcut]
        tauto
    | exceptional j =>
      cases v with
      | ordinary r =>
        simp only [coordinateEdges, cliqueLift, coordinateCollapse, f, reduceCtorEq,
          false_or, exceptional_lt_ordinary, Function.comp_apply]
        have hpos : e (p j) < r ↔ p j < rankCeil e he r := by
          have := rankCeil_le_iff e he r (p j)
          omega
        have hcut : e (c j) < r ↔ c j < rankCeil e he r := by
          have := rankCeil_le_iff e he r (c j)
          omega
        rw [hpos, hcut]
        tauto
      | exceptional k =>
        simp only [coordinateEdges, cliqueLift, coordinateCollapse, f,
          exceptional_lt_exceptional, Function.comp_apply, he.lt_iff_lt,
          he.injective.eq_iff, CoordinateVertex.exceptional.injEq]
        constructor
        · rintro ⟨hjk, hB⟩
          exact ⟨hjk, Or.inr ⟨hjk, hB⟩⟩
        · rintro ⟨hjk, heq | ⟨_, hB⟩⟩
          · subst k
            simp at hjk
          · exact ⟨hjk, hB⟩
  rw [hgraph]
  exact rules_cliqueLift_iff (fun h => h.1) (coordinateCollapse_monotone p e he)
    (coordinateSection_strictMono p e he) hfs

/-- Fill every edge ending outside a specified initial segment. -/
def universalTail {α : Type*} [LinearOrder α] (E : α → α → Prop)
    (S : α → Prop) (a b : α) : Prop := a < b ∧ (¬ S b ∨ E a b)

private theorem rules_universalTail_iff {α : Type*} [LinearOrder α]
    {E : α → α → Prop} {S : α → Prop}
    (hdown : ∀ {a b}, a ≤ b → S b → S a)
    (hbound : ∀ {a b}, E a b → a < b ∧ S b) :
    Rules (universalTail E S) ↔ Rules E := by
  constructor
  · intro h
    have lift {a b : α} (hab : E a b) : universalTail E S a b :=
      ⟨(hbound hab).1, Or.inr hab⟩
    have unlift {a b : α} (hab : universalTail E S a b) (hb : S b) : E a b :=
      hab.2.resolve_left (not_not.mpr hb)
    refine ⟨fun hab => (hbound hab).1, ?_, ?_⟩
    · intro a b c d hab hcd hac hcb hbd
      exact unlift (h.propagate (lift hab) (lift hcd) hac hcb hbd) (hbound hcd).2
    · intro a b c d e f hab hcd hef hac hcb hae heb hbd hbf
      have hmax : S (max d f) := by
        rcases le_total d f with hdf | hfd
        · simpa only [max_eq_right hdf] using (hbound hef).2
        · simpa only [max_eq_left hfd] using (hbound hcd).2
      exact unlift (h.join (lift hab) (lift hcd) (lift hef) hac hcb hae heb hbd hbf) hmax
  · intro h
    refine ⟨fun hab => hab.1, ?_, ?_⟩
    · intro a b c d hab hcd hac hcb hbd
      refine ⟨hbd, ?_⟩
      by_cases hd : S d
      · right
        have hb := hdown hbd.le hd
        exact h.propagate (hab.2.resolve_left (not_not.mpr hb))
          (hcd.2.resolve_left (not_not.mpr hd)) hac hcb hbd
      · exact Or.inl hd
    · intro a b c d e f hab hcd hef hac hcb hae heb hbd hbf
      refine ⟨(max_lt hcb heb).trans_le (hbd.trans (le_max_left d f)), ?_⟩
      by_cases hm : S (max d f)
      · right
        have hd := hdown (le_max_left d f) hm
        have hf := hdown (le_max_right d f) hm
        have hb := hdown hbd hd
        exact h.join (hab.2.resolve_left (not_not.mpr hb))
          (hcd.2.resolve_left (not_not.mpr hd)) (hef.2.resolve_left (not_not.mpr hf))
          hac hcb hae heb hbd hbf
      · exact Or.inl hm

/-- The finite vertex segment containing ordinary ranks through M and every exception. -/
def coordinateInside {i : ℕ} {p : Fin i → ℕ} (M : ℕ) : CoordinateVertex p → Prop
  | .ordinary r => r ≤ M
  | .exceptional _ => True

/-- Restrict coordinate edges to the finite vertex segment, without adding vertices. -/
def boundedCoordinateEdges {i : ℕ} (M : ℕ) (p c : Fin i → ℕ)
    (B : Fin i → Fin i → Prop) (u v : CoordinateVertex p) : Prop :=
  coordinateEdges p c B u v ∧ coordinateInside M v

theorem coordinateInside_downward {i : ℕ} (M : ℕ) (p : Fin i → ℕ)
  (hp : ∀ j, p j ≤ M) : ∀ {u v : CoordinateVertex p}, u ≤ v →
    coordinateInside M v → coordinateInside M u := by
  intro u v huv hv
  cases u with
  | exceptional j => trivial
  | ordinary r =>
    cases v with
    | ordinary s =>
      have hrs : r ≤ s := by
        by_contra h
        exact (not_lt_of_ge huv) ((ordinary_lt_ordinary _ _).mpr (by omega))
      exact hrs.trans hv
    | exceptional j =>
      have hrp : r ≤ p j := by
        by_contra h
        exact (not_lt_of_ge huv) ((exceptional_lt_ordinary _ _).mpr (by omega))
      exact hrp.trans (hp j)

/-- Finite coordinate admissibility is independent of the universal ordinary tail.
All zero and tied coordinates and the case M=0 are included. -/
theorem coordinate_rules_bounded_iff {i : ℕ} (M : ℕ) (p c : Fin i → ℕ)
    (B : Fin i → Fin i → Prop) (hp : ∀ j, p j ≤ M) (hc : ∀ j, c j ≤ M) :
    Rules (boundedCoordinateEdges M p c B) ↔ Rules (coordinateEdges p c B) := by
  have hdown := @coordinateInside_downward i M p hp
  have heq : coordinateEdges p c B =
      universalTail (boundedCoordinateEdges M p c B) (coordinateInside M) := by
    funext u v
    apply propext
    constructor
    · intro huv
      refine ⟨huv.1, ?_⟩
      by_cases hv : coordinateInside M v
      · exact Or.inr ⟨huv, hv⟩
      · exact Or.inl hv
    · rintro ⟨huv, hv | hv⟩
      · cases v with
        | exceptional j => exact False.elim (hv trivial)
        | ordinary r =>
          have hMr : M < r := by simpa only [coordinateInside, not_le] using hv
          refine ⟨huv, ?_⟩
          cases u with
          | ordinary s => trivial
          | exceptional j => exact (hc j).trans_lt hMr
      · exact hv.1
  rw [heq]
  exact (rules_universalTail_iff hdown (fun h => ⟨h.1.1, h.2⟩)).symm

/-- The finite coordinate vertex set, with its inherited lexicographic order. -/
abbrev BoundedCoordinateVertex {i : ℕ} (M : ℕ) (p : Fin i → ℕ) :=
  {u : CoordinateVertex p // coordinateInside M u}

private def sourceCoordinateMap {M i : ℕ} {p : Fin i → ℕ}
    (g : Fin M → ℕ) (s : Fin i → ℕ) : BoundedCoordinateVertex M p → ℕ
  | ⟨.ordinary r, hr⟩ => if hz : r = 0 then 0 else
      g ⟨r - 1, by change r ≤ M at hr; omega⟩
  | ⟨.exceptional j, _⟩ => s j

private theorem sourceCoordinateMap_strictMono {M i : ℕ} {p : Fin i → ℕ}
    (g : Fin M → ℕ) (s : Fin i → ℕ) (hg : StrictMono g) (hs : StrictMono s)
    (hgp : ∀ r, 0 < g r) (hsp : ∀ j, 0 < s j) (hpm : Monotone p)
    (hp : ∀ j, Position g (s j) (p j)) : StrictMono (sourceCoordinateMap (p := p) g s) := by
  intro ⟨u, hu⟩ ⟨v, hv⟩ huv
  change u < v at huv
  cases u with
  | ordinary r =>
    cases v with
    | ordinary t =>
      have hrt := (ordinary_lt_ordinary r t).mp huv
      change r ≤ M at hu
      change t ≤ M at hv
      simp only [sourceCoordinateMap]
      split_ifs with hr ht
      · omega
      · exact hgp _
      · omega
      · apply hg
        change r - 1 < t - 1
        omega
    | exceptional j =>
      have hrp := (ordinary_lt_exceptional r j).mp huv
      change r ≤ M at hu
      simp only [sourceCoordinateMap]
      split_ifs with hr
      · exact hsp j
      · exact ((hp j).2 ⟨r - 1, by omega⟩).1.mpr (by change r - 1 < p j; omega)
  | exceptional j =>
    cases v with
    | ordinary r =>
      have hpr := (exceptional_lt_ordinary j r).mp huv
      change r ≤ M at hv
      simp only [sourceCoordinateMap]
      rw [dif_neg (by omega)]
      exact ((hp j).2 ⟨r - 1, by omega⟩).2.mpr (by change p j ≤ r - 1; omega)
    | exceptional k =>
      have hjk := (exceptional_lt_exceptional j k).mp huv
      apply hs
      rcases hjk with h | ⟨_, h⟩
      · by_contra hh
        have := hpm (le_of_not_gt hh)
        omega
      · exact h

private theorem sourceCoordinateMap_edges {M i : ℕ} {p c : Fin i → ℕ}
    {E : ℕ → ℕ → Prop} (hE : Rules E)
    (g : Fin M → ℕ) (s : Fin i → ℕ)
    (hf : StrictMono (sourceCoordinateMap (p := p) g s))
    (ho : ∀ r, E 0 (g r)) (hm : ∀ j, ¬ E 0 (s j))
    (hc : ∀ j, Cutoff E g (s j) (c j))
    (u v : BoundedCoordinateVertex M p) :
    E (sourceCoordinateMap g s u) (sourceCoordinateMap g s v) ↔
      coordinateEdges p c (fun j k => E (s j) (s k)) u.val v.val := by
  have hord : E (sourceCoordinateMap g s u) (sourceCoordinateMap g s v) → u < v :=
    fun h => hf.lt_iff_lt.mp (hE.ordered h)
  constructor
  · intro he
    refine ⟨hord he, ?_⟩
    rcases u with ⟨u, hu⟩
    rcases v with ⟨v, hv⟩
    cases u with
    | ordinary r =>
      cases v with
      | ordinary t => trivial
      | exceptional j =>
        by_cases hr : r = 0
        · exact False.elim (hm j (by simpa only [sourceCoordinateMap, dif_pos hr] using he))
        · have hi : Incident E (s j) (g ⟨r - 1, by change r ≤ M at hu; omega⟩) :=
            Or.inr (by simpa only [sourceCoordinateMap, dif_neg hr] using he)
          have hcut := ((hc j).2 _).mp hi
          change c j ≤ r - 1 at hcut
          change r ≤ M at hu
          change c j < r
          omega
    | exceptional j =>
      cases v with
      | ordinary r =>
        by_cases hr : r = 0
        · have hh : E (s j) 0 := by simpa only [sourceCoordinateMap, dif_pos hr] using he
          have := hE.ordered hh
          omega
        · have hi : Incident E (s j) (g ⟨r - 1, by change r ≤ M at hv; omega⟩) :=
            Or.inl (by simpa only [sourceCoordinateMap, dif_neg hr] using he)
          have hcut := ((hc j).2 _).mp hi
          change c j ≤ r - 1 at hcut
          change r ≤ M at hv
          change c j < r
          omega
      | exceptional k => exact he
  · intro he
    have hlt := hf he.1
    rcases u with ⟨u, hu⟩
    rcases v with ⟨v, hv⟩
    cases u with
    | ordinary r =>
      cases v with
      | ordinary t =>
        change r ≤ M at hu
        change t ≤ M at hv
        simp only [sourceCoordinateMap] at hlt ⊢
        split_ifs at hlt ⊢ with hr ht
        · omega
        · exact ho _
        · omega
        · exact hE.propagate (ho _) (ho _) le_rfl (hE.ordered (ho _)) hlt
      | exceptional j =>
        have hcr : c j < r := he.2
        have hr : r ≠ 0 := by omega
        have hi := ((hc j).2 ⟨r - 1, by change r ≤ M at hu; omega⟩).mpr (by change c j ≤ r - 1; omega)
        simp only [sourceCoordinateMap, dif_neg hr] at hlt ⊢
        exact hi.resolve_left (fun hh => (not_lt_of_ge hlt.le) (hE.ordered hh))
    | exceptional j =>
      cases v with
      | ordinary r =>
        have hcr : c j < r := he.2
        have hr : r ≠ 0 := by omega
        have hi := ((hc j).2 ⟨r - 1, by change r ≤ M at hv; omega⟩).mpr (by change c j ≤ r - 1; omega)
        simp only [sourceCoordinateMap, dif_neg hr] at hlt ⊢
        exact hi.resolve_right (fun hh => (not_lt_of_ge hlt.le) (hE.ordered hh))
      | exceptional k => exact he.2

/-- Every literal source graph is exactly its finite coordinate graph, by an increasing
bijection preserving all exceptional-edge bits. No coordinate is required positive or distinct. -/
theorem edgeFamily_coordinate_realization {n i : ℕ} (hi : i ≤ n + 1)
    {A : Finset (ℕ × ℕ)} (hA : A ∈ edgeFamily n (n + 1 - i)) :
    ∃ (p c : Fin i → ℕ) (B : Fin i → Fin i → Prop)
      (f : BoundedCoordinateVertex (n + 1 - i) p → ℕ),
      Monotone p ∧ (∀ j, p j ≤ n + 1 - i) ∧ (∀ j, c j ≤ n + 1 - i) ∧
      (∀ j k, B j k → j < k) ∧ StrictMono f ∧ (∀ u, f u ≤ n + 1) ∧
      (∀ a, a ≤ n + 1 → ∃ u, f u = a) ∧
      (∀ u v, (f u, f v) ∈ A ↔ coordinateEdges p c B u.val v.val) := by
  classical
  obtain ⟨g, s, p, c, hg, hs, hpm, ha, hsm, hcover, hp, hc, _⟩ :=
    edgeFamily_has_coordinates hi hA
  have hE : Rules (fun a b => (a, b) ∈ A) := (Finset.mem_filter.mp hA).2.1
  have hgp : ∀ r, 0 < g r := fun r => hE.ordered ((ha _).mpr ⟨r, rfl⟩)
  have hgb : ∀ r, g r ≤ n + 1 := by
    intro r
    have he := (ha _).mpr ⟨r, rfl⟩
    have hb := (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1) he
    have hb' := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_filter.mp hb).1).2
    omega
  let f := sourceCoordinateMap (p := p) g s
  have hf : StrictMono f := sourceCoordinateMap_strictMono g s hg hs hgp
    (fun j => (hsm j).2.1) hpm hp
  refine ⟨p, c, (fun j k => (s j, s k) ∈ A), f, hpm,
    (fun j => (hp j).1), (fun j => (hc j).1),
    (fun j k he => hs.lt_iff_lt.mp (hE.ordered he)), hf, ?_, ?_, ?_⟩
  · rintro ⟨u, hu⟩
    cases u with
    | ordinary r =>
      simp only [f, sourceCoordinateMap]
      split_ifs
      · omega
      · exact hgb _
    | exceptional j => exact (hsm j).2.2
  · intro a haN
    by_cases haz : a = 0
    · exact ⟨⟨.ordinary 0, Nat.zero_le _⟩, by simp [f, sourceCoordinateMap, haz]⟩
    rcases hcover a (Nat.pos_of_ne_zero haz) haN with ⟨r, rfl⟩ | ⟨j, rfl⟩
    · refine ⟨⟨.ordinary (r.val + 1), by change r.val + 1 ≤ n + 1 - i; omega⟩, ?_⟩
      simp only [f, sourceCoordinateMap, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ↓reduceDIte, Nat.add_sub_cancel]
    · exact ⟨⟨.exceptional j, trivial⟩, rfl⟩
  · exact sourceCoordinateMap_edges hE g s hf (fun r => (ha _).mpr ⟨r, rfl⟩)
      (fun j => (hsm j).1) hc

private def positionCount {i : ℕ} (p : Fin i → ℕ) (r : ℕ) : ℕ :=
  (Finset.univ.filter (fun j => p j < r)).card

private theorem positionCount_le {i : ℕ} (p : Fin i → ℕ) (r : ℕ) :
    positionCount p r ≤ i := by
  simpa only [positionCount, Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_le (Finset.univ : Finset (Fin i)) (fun j => p j < r)

private theorem positionCount_mono {i : ℕ} (p : Fin i → ℕ) : Monotone (positionCount p) := by
  intro r s hrs
  apply Finset.card_le_card
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.trans_le hrs⟩

private theorem index_lt_positionCount {i : ℕ} (p : Fin i → ℕ) (hpm : Monotone p)
    (r : ℕ) (j : Fin i) : j.val < positionCount p r ↔ p j < r :=
  Fin.lt_card_filter_univ_iff_apply_of_imp (fun j => p j < r)
    (fun j k hkj hj => (hpm hkj).trans_lt hj)

/-- The natural label of a coordinate vertex. The exceptional formula counts earlier
ordinary vertices and earlier exceptions; the ordinary formula counts earlier exceptions. -/
def coordinateLabel {i : ℕ} (p : Fin i → ℕ) : CoordinateVertex p → ℕ
  | .ordinary r => r + positionCount p r
  | .exceptional j => p j + j.val + 1

theorem coordinateLabel_strictMono {i : ℕ} (p : Fin i → ℕ) (hpm : Monotone p) :
    StrictMono (coordinateLabel p) := by
  intro u v huv
  cases u with
  | ordinary r =>
    cases v with
    | ordinary s =>
      have hrs := (ordinary_lt_ordinary r s).mp huv
      have := positionCount_mono p hrs.le
      change r + positionCount p r < s + positionCount p s
      omega
    | exceptional j =>
      have hrp := (ordinary_lt_exceptional r j).mp huv
      have hcount : positionCount p r ≤ j.val := by
        have := index_lt_positionCount p hpm r j
        omega
      change r + positionCount p r < p j + j.val + 1
      omega
  | exceptional j =>
    cases v with
    | ordinary r =>
      have hpr := (exceptional_lt_ordinary j r).mp huv
      have hcount := (index_lt_positionCount p hpm r j).mpr hpr
      change p j + j.val + 1 < r + positionCount p r
      omega
    | exceptional k =>
      have hjk := (exceptional_lt_exceptional j k).mp huv
      have hjk' : j < k := by
        rcases hjk with h | ⟨_, h⟩
        · by_contra hh
          have := hpm (le_of_not_gt hh)
          omega
        · exact h
      have := hpm hjk'.le
      have := hjk'
      change p j + j.val + 1 < p k + k.val + 1
      omega

private def boundedVertexEquiv {i : ℕ} (M : ℕ) (p : Fin i → ℕ) :
    BoundedCoordinateVertex M p ≃ (Fin (M + 1) ⊕ Fin i) where
  toFun u := match u with
    | ⟨.ordinary r, hr⟩ => .inl ⟨r, by change r ≤ M at hr; omega⟩
    | ⟨.exceptional j, _⟩ => .inr j
  invFun u := match u with
    | .inl r => ⟨.ordinary r.val, by change r.val ≤ M; omega⟩
    | .inr j => ⟨.exceptional j, trivial⟩
  left_inv := by rintro ⟨u, hu⟩; cases u <;> rfl
  right_inv := by intro u; cases u <;> rfl

noncomputable instance boundedCoordinateFintype {i : ℕ} (M : ℕ) (p : Fin i → ℕ) :
    Fintype (BoundedCoordinateVertex M p) :=
  Fintype.ofEquiv (Fin (M + 1) ⊕ Fin i) (boundedVertexEquiv M p).symm

theorem coordinateLabel_bound {i M : ℕ} (p : Fin i → ℕ)
    (hp : ∀ j, p j ≤ M) (u : BoundedCoordinateVertex M p) : coordinateLabel p u.val ≤ M + i := by
  rcases u with ⟨u, hu⟩
  cases u with
  | ordinary r =>
    change r ≤ M at hu
    have := positionCount_le p r
    change r + positionCount p r ≤ M + i
    omega
  | exceptional j =>
    have := hp j
    have := j.isLt
    change p j + j.val + 1 ≤ M + i
    omega

/-- Every bounded weak position list labels its coordinate vertices increasingly and
bijectively by 0 through M+i, including M=i=0. -/
theorem coordinateLabel_bijective {i M : ℕ} (p : Fin i → ℕ) (hpm : Monotone p)
    (hp : ∀ j, p j ≤ M) :
    Function.Bijective (fun u : BoundedCoordinateVertex M p =>
      (⟨coordinateLabel p u.val, by have := coordinateLabel_bound p hp u; omega⟩ : Fin (M + i + 1))) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, ?_⟩
  · intro u v h
    apply Subtype.ext
    exact (coordinateLabel_strictMono p hpm).injective (congrArg Fin.val h)
  · rw [Fintype.card_congr (boundedVertexEquiv M p)]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega

end D5.S3.Combinatorics.MazorchukXu
