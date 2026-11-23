/- GID: D5/S3/Combinatorics/Matroids/RankThreeOptimalInternalLatin
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankThreeOptimalInternalLatin
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Optimal ternary internal triple families are described by rowwise Latin squares. -/

import D5.S3.Combinatorics.Matroids.RankThreeMinimumInternalAdditions
import D5.S3.Combinatorics.LatinEulerianDefs

/-! The Latin-square coordinates of optimal internal triple families. -/

noncomputable section
namespace D5.S3.Combinatorics.Matroids.RankThreeOptimalInternalLatin

open RankThreeInternalTriplePotentials (Row AllowsExtra cyclicReduction LiftedLineFamily
  potential_finrank_internal_triples)
open RankThreeOmissionPotentialFibers (potentialSpace)
open RankThreeOmissionPotentials (covers)
open D5.S3.Combinatorics.LatinEulerianMultiples (IsLatin)

private theorem rowwise_slot_saturation {d r : ℕ} [NeZero (3 * r)] {T U : Type*}
    [Fintype U]
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    (he : ∀ x a, (e x a).1 = ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) a)
    (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (internal : U → Fin 3 → Row d × ZMod (3 * r))
    (distinct_rows : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (extra : AllowsExtra (Sum.elim mixed internal))
    (count : Fintype.card U = 3^d * r^2) :
    ∀ u, Function.Injective (fun i => cyclicReduction (3 * r) (internal u i).2) := by
  classical
  let reduce := ZMod.castHom (dvd_mul_right 3 r) (ZMod 3)
  have residue (x : Row d) (a : ZMod 3) (i : Fin r) :
      reduce ((e x).symm (a, i)) = a := by
    rw [← he x, (e x).apply_symm_apply]
  have reduction_eq : cyclicReduction (3 * r) = reduce.toAddMonoidHom := by
    unfold cyclicReduction
    rw [dite_eq_left (dvd_mul_right 3 r)]
  have uncovered := extra.2.1
  rw [reduction_eq] at uncovered
  let Labels := {p : ZMod 3 × ZMod 3 // p.1 ≠ p.2}
  let Slots := {p : Fin 3 × Fin 3 // p.1 ≠ p.2}
  let Pairs := Row d × (Labels × (Fin r × Fin r))
  let left (p : Pairs) : Row d × ZMod (3 * r) := (p.1, (e p.1).symm (p.2.1.val.1,p.2.2.1))
  let right (p : Pairs) : Row d × ZMod (3 * r) := (p.1, (e p.1).symm (p.2.1.val.2,p.2.2.2))
  have different (p : Pairs) : reduce (left p).2 ≠ reduce (right p).2 := by
    simpa only [left,right,residue] using p.2.1.prop
  have cover (p : Pairs) : ∃ u i j, internal u i = left p ∧ internal u j = right p := by
    have h : ∃ t, covers (Sum.elim mixed internal t) (left p) (right p) := by
      by_contra missing
      have zero := uncovered p.1 (left p).2 (right p).2 missing
      change reduce ((left p).2 - (right p).2) = 0 at zero
      rw [map_sub, sub_eq_zero] at zero
      exact different p zero
    obtain ⟨t,i,j,hi,hj⟩ := h
    cases t with
    | inr u => exact ⟨u,i,j,hi,hj⟩
    | inl t =>
      have ij : i = j := distinct_rows t ((congrArg Prod.fst hi).trans
        (congrArg Prod.fst hj).symm)
      subst j
      exact False.elim (different p (congrArg (fun a => reduce a.2) (hi.symm.trans hj)))
  choose triple i j hi hj using cover
  let toSlots (p : Pairs) : U × Slots :=
    (triple p, ⟨(i p, j p), by
      intro eq
      change i p = j p at eq
      have same := (hi p).symm.trans ((congrArg (internal (triple p)) eq).trans (hj p))
      exact different p (congrArg (fun a => reduce a.2) same)⟩)
  have injective : Function.Injective toSlots := by
    intro p q equality
    have ht : triple p = triple q := congrArg Prod.fst equality
    have hslots : (i p, j p) = (i q, j q) :=
      congrArg (fun (v : U × Slots) => v.2.val) equality
    have hLeft : left p = left q := by
      rw [← hi p, ← hi q, ht, show i p = i q from congrArg Prod.fst hslots]
    have hRight : right p = right q := by
      rw [← hj p, ← hj q, ht, show j p = j q from congrArg Prod.snd hslots]
    have sameRow : p.1 = q.1 := congrArg (fun z : Row d × ZMod (3 * r) => z.1) hLeft
    have firstRaw := congrArg Prod.snd hLeft
    have secondRaw := congrArg Prod.snd hRight
    change (e p.1).symm (p.2.1.val.1, p.2.2.1) =
      (e q.1).symm (q.2.1.val.1, q.2.2.1) at firstRaw
    change (e p.1).symm (p.2.1.val.2, p.2.2.2) =
      (e q.1).symm (q.2.1.val.2, q.2.2.2) at secondRaw
    rw [← sameRow] at firstRaw secondRaw
    have first := (e p.1).symm.injective firstRaw
    have second := (e p.1).symm.injective secondRaw
    have firstLabel := congrArg Prod.fst first
    have secondLabel := congrArg Prod.fst second
    have firstIndex := congrArg Prod.snd first
    have secondIndex := congrArg Prod.snd second
    have sameLabels : p.2.1 = q.2.1 := Subtype.ext (Prod.ext firstLabel secondLabel)
    have sameIndices : p.2.2 = q.2.2 := Prod.ext firstIndex secondIndex
    exact Prod.ext sameRow (Prod.ext sameLabels sameIndices)
  have labelsCard : Fintype.card Labels = 6 := by decide
  have slotsCard : Fintype.card Slots = 6 := by decide

  have sameCard : Fintype.card Pairs = Fintype.card (U × Slots) := by
    change Fintype.card (Row d × (Labels × (Fin r × Fin r))) =
      Fintype.card (U × Slots)
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, ZMod.card,
      labelsCard, slotsCard, Row, count]
    ring
  have onto := ((Fintype.bijective_iff_injective_and_card toSlots).mpr
    ⟨injective, sameCard⟩).2
  intro u a b same
  by_contra differentSlots
  obtain ⟨p, hp⟩ := onto (u, ⟨(a, b), differentSlots⟩)
  have hu : triple p = u := congrArg Prod.fst hp
  have slotsEq : (i p, j p) = (a, b) := congrArg (fun (v : U × Slots) => v.2.val) hp
  have hl := hi p
  have hr := hj p
  rw [hu, show i p = a from congrArg Prod.fst slotsEq] at hl
  rw [hu, show j p = b from congrArg Prod.snd slotsEq] at hr
  rw [reduction_eq] at same
  change reduce (internal u a).2 = reduce (internal u b).2 at same
  rw [hl, hr] at same
  exact different p same

private theorem rowwise_forced_pairs {d r : ℕ} {T U : Type*} [NeZero (3 * r)]
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    (he : ∀ x a, (e x a).1 = ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) a)
    (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (internal : U → Fin 3 → Row d × ZMod (3 * r))
    (distinctRows : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (extra : AllowsExtra (Sum.elim mixed internal))
    (pairUnique : ∀ t u x y, x ≠ y → covers (Sum.elim mixed internal t) x y →
      covers (Sum.elim mixed internal u) x y → t = u) :
    ∀ (x : Row d) (i j : Fin 3), i ≠ j → ∀ a b : Fin r,
      ∃! u, covers (internal u) (x, (e x).symm (ZMod.finEquiv 3 i, a))
        (x, (e x).symm (ZMod.finEquiv 3 j, b)) := by
  classical
  let red := ZMod.castHom (dvd_mul_right 3 r) (ZMod 3)
  have red_eq : cyclicReduction (3 * r) = red.toAddMonoidHom := by
    unfold cyclicReduction
    rw [dite_eq_left (dvd_mul_right 3 r)]
  have uncovered := extra.2.1
  rw [red_eq] at uncovered
  intro x i j different a b
  let left := (e x).symm (ZMod.finEquiv 3 i, a)
  let right := (e x).symm (ZMod.finEquiv 3 j, b)
  have diffRed : red left ≠ red right := by
    rw [← he x, ← he x]
    change (e x ((e x).symm (ZMod.finEquiv 3 i, a))).1 ≠ (e x ((e x).symm (ZMod.finEquiv 3 j, b))).1
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact (ZMod.finEquiv 3).injective.ne different
  have covered : ∃ t, covers (Sum.elim mixed internal t) (x,left) (x,right) := by
    by_contra missing
    have zero := uncovered x left right missing
    change red (left - right) = 0 at zero
    rw [map_sub, sub_eq_zero] at zero
    exact diffRed zero
  have notMixed (t : T) (h : covers (mixed t) (x,left) (x,right)) : False := by
    obtain ⟨k,l,hk,hl⟩ := h
    have eq := distinctRows t ((congrArg Prod.fst hk).trans (congrArg Prod.fst hl).symm)
    subst l
    exact diffRed (congrArg (fun p => red p.2) (hk.symm.trans hl))
  rcases covered with ⟨t, ht⟩
  cases t with
  | inl t => exact (notMixed t ht).elim
  | inr t =>
    refine ⟨t, ht, ?_⟩
    intro u hu
    have distinctPts : ((x,left) : Row d × ZMod (3 * r)) ≠ (x,right) :=
      fun eq => diffRed (congrArg (fun p => red p.2) eq)
    exact Sum.inr.inj (pairUnique (Sum.inr u) (Sum.inr t) _ _ distinctPts hu ht)

private theorem rowwise_residue_reordering {d r : ℕ} {U : Type*} [NeZero (3 * r)]
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    (internal : U → Fin 3 → Row d × ZMod (3 * r))
    (sameRow : ∀ u i, (internal u i).1 = (internal u 0).1)
    (injLabels : ∀ u, Function.Injective (fun i => (e (internal u 0).1 (internal u i).2).1))
    (pairs : ∀ (x : Row d) (i j : Fin 3), i ≠ j → ∀ a b : Fin r,
      ∃! u, covers (internal u) (x,(e x).symm (ZMod.finEquiv 3 i,a))
        (x,(e x).symm (ZMod.finEquiv 3 j,b))) :
    ∃ (row : U → Row d) (label : U → Fin 3 → Fin r),
      (∀ u, Set.range (internal u) = Set.range
        (fun i : Fin 3 => (row u, (e (row u)).symm (ZMod.finEquiv 3 i, label u i)))) ∧
      (∀ x i j, i ≠ j → ∀ a b, ∃! u, row u = x ∧ label u i = a ∧ label u j = b) := by
  classical
  let residue (u : U) (j : Fin 3) := (ZMod.finEquiv 3).symm (e (internal u 0).1 (internal u j).2).1
  have bij (u : U) : Function.Bijective (residue u) :=
    (Finite.injective_iff_bijective).mp ((ZMod.finEquiv 3).symm.injective.comp (injLabels u))
  let reorder (u : U) := Equiv.ofBijective (residue u) (bij u)
  let row (u : U) := (internal u 0).1
  let label (u : U) (i : Fin 3) := (e (row u) (internal u ((reorder u).symm i)).2).2
  let pt (x : Row d) (i : Fin 3) (a : Fin r) := (x, (e x).symm (ZMod.finEquiv 3 i, a))
  have normalized (u : U) (i : Fin 3) : internal u ((reorder u).symm i) = pt (row u) i (label u i) := by
    refine Prod.ext (sameRow u _) ?_
    change (internal u ((reorder u).symm i)).2 = (e (row u)).symm (ZMod.finEquiv 3 i, label u i)
    apply (e (row u)).injective
    rw [Equiv.apply_symm_apply]
    have h := (reorder u).apply_symm_apply i
    change (ZMod.finEquiv 3).symm (e (row u) (internal u ((reorder u).symm i)).2).1 = i at h
    exact Prod.ext ((ZMod.finEquiv 3).symm_apply_eq.mp h) rfl
  have index (u : U) (i : Fin 3) (x : Row d) (a : Fin r) :
      pt x i a ∈ Set.range (internal u) ↔ row u = x ∧ label u i = a := by
    constructor
    · rintro ⟨j, hj⟩
      have hp : internal u ((reorder u).symm ((reorder u) j)) = pt x i a := by
        rw [Equiv.symm_apply_apply, hj]
      rw [normalized] at hp
      have hrow : row u = x := congrArg Prod.fst hp
      have hz := congrArg Prod.snd hp
      change (e (row u)).symm (ZMod.finEquiv 3 ((reorder u) j), label u ((reorder u) j)) =
        (e x).symm (ZMod.finEquiv 3 i, a) at hz
      rw [← hrow] at hz
      have hlabel := (e (row u)).symm.injective hz
      have hslot : (reorder u) j = i :=
        (ZMod.finEquiv 3).injective (congrArg Prod.fst hlabel)
      have hid := congrArg Prod.snd hlabel
      rw [hslot] at hid
      exact ⟨hrow, hid⟩
    · rintro ⟨hrow, hlabel⟩
      exact ⟨(reorder u).symm i, by rw [normalized, hrow, hlabel]⟩
  refine ⟨row, label, ?_, ?_⟩
  · intro u
    ext p
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨reorder u j, ?_⟩
      change pt (row u) (reorder u j) (label u (reorder u j)) = internal u j
      rw [← normalized, Equiv.symm_apply_apply]
    · rintro ⟨j, rfl⟩
      exact ⟨(reorder u).symm j, normalized u j⟩
  · intro x i j different a b
    apply (existsUnique_congr (fun u => ?_)).mp (pairs x i j different a b)
    constructor
    · rintro ⟨k, l, hk, hl⟩
      exact ⟨((index u i x a).mp ⟨k, hk⟩).1,
        ((index u i x a).mp ⟨k, hk⟩).2, ((index u j x b).mp ⟨l, hl⟩).2⟩
    · rintro ⟨hx, ha, hb⟩
      obtain ⟨k, hk⟩ := (index u i x a).mpr ⟨hx, ha⟩
      obtain ⟨l, hl⟩ := (index u j x b).mpr ⟨hx, hb⟩
      exact ⟨k, l, hk, hl⟩

private theorem latin_ordered_projection {U X : Type*} {r : ℕ}
    (row : U → X) (label : U → Fin 3 → Fin r)
    (covers : ∀ x (i j : Fin 3), i ≠ j → ∀ a b : Fin r,
      ∃! u, row u = x ∧ label u i = a ∧ label u j = b)
    (x : X) :
    let R := fun a b c => ∃ u, row u = x ∧
      label u 0 = a ∧ label u 1 = b ∧ label u 2 = c
    (∀ a b, ∃! c, R a b c) ∧ (∀ a c, ∃! b, R a b c) ∧ (∀ b c, ∃! a, R a b c) := by
  intro R
  have completion (i j k : Fin 3) (ij : i ≠ j) (a b : Fin r) :
      ∃! c, ∃ u, row u = x ∧ label u i = a ∧ label u j = b ∧ label u k = c := by
    obtain ⟨u, hu, hunique⟩ := covers x i j ij a b
    refine ⟨label u k, ⟨u, hu.1, hu.2.1, hu.2.2, rfl⟩, ?_⟩
    rintro c ⟨v, hrow, hi, hj, hk⟩
    have eq := hunique v ⟨hrow, hi, hj⟩
    simpa only [eq] using hk.symm
  refine ⟨fun a b => completion 0 1 2 (by decide) a b, ?_, ?_⟩
  · intro a c
    apply (existsUnique_congr (fun b => ?_)).mp (completion 0 2 1 (by decide) a c)
    simp only [R, and_comm]
  · intro b c
    apply (existsUnique_congr (fun a => ?_)).mp (completion 1 2 0 (by decide) b c)
    simp only [R, and_comm, and_left_comm]

private theorem latin_of_projections {r : ℕ} (R : Fin r → Fin r → Fin r → Prop)
    (h01 : ∀ a b, ∃! c, R a b c)
    (h02 : ∀ a c, ∃! b, R a b c)
    (h12 : ∀ b c, ∃! a, R a b c) :
    ∃! L, IsLatin r L ∧ ∀ a b c, R a b c ↔ L a b = c := by
  classical
  let L (a b : Fin r) := (h01 a b).choose
  have graph (a b c : Fin r) : R a b c ↔ L a b = c := by
    constructor
    · intro h
      exact ((h01 a b).choose_spec.2 c h).symm
    · intro h
      rw [← h]
      exact (h01 a b).choose_spec.1
  have latin : IsLatin r L := by
    constructor
    · intro a
      constructor
      · intro b₁ b₂ eq
        obtain ⟨b, _, unique⟩ := h02 a (L a b₁)
        exact (unique b₁ ((graph a b₁ _).mpr rfl)).trans
          (unique b₂ ((graph a b₂ _).mpr eq.symm)).symm
      · intro c
        obtain ⟨b, hb, _⟩ := h02 a c
        exact ⟨b, (graph a b c).mp hb⟩
    · intro b
      constructor
      · intro a₁ a₂ eq
        obtain ⟨a, _, unique⟩ := h12 b (L a₁ b)
        exact (unique a₁ ((graph a₁ b _).mpr rfl)).trans
          (unique a₂ ((graph a₂ b _).mpr eq.symm)).symm
      · intro c
        obtain ⟨a, ha, _⟩ := h12 b c
        exact ⟨a, (graph a b c).mp ha⟩
  refine ⟨L, ⟨latin, graph⟩, ?_⟩
  intro K hk
  funext a b
  exact (hk.2 a b (L a b)).mp ((graph a b _).mpr rfl)


/-- The three points specified by a cell in the Latin square of its row. -/
def latinPoint {d r : ℕ}
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    (L : Row d → Fin r → Fin r → Fin r)
    (u : Row d × (Fin r × Fin r)) (i : Fin 3) : Row d × ZMod (3 * r) :=
  (u.1, (e u.1).symm (ZMod.finEquiv 3 i, ![u.2.1, u.2.2, L u.1 u.2.1 u.2.2] i))

/-- Every minimum family giving the extra dimension is generated by rowwise Latin squares. -/
theorem exists_latin_of_optimal_family {d r : ℕ} {T U : Type*} [NeZero (3 * r)] [Fintype U]
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    (he : ∀ x a, (e x a).1 = ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) a)
    (hd : 0 < d) (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (internal : U → Fin 3 → Row d × ZMod (3 * r))
    (family : LiftedLineFamily (Sum.elim mixed internal))
    (distinctRows : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (sameRow : ∀ u i, (internal u i).1 = (internal u 0).1)
    (pairUnique : ∀ t u x y, x ≠ y → covers (Sum.elim mixed internal t) x y →
      covers (Sum.elim mixed internal u) x y → t = u)
    (dim : Module.finrank (ZMod 3) (potentialSpace (Sum.elim mixed internal) 0) = d + 1)
    (count : Fintype.card U = 3 ^ d * r ^ 2) :
    ∃ L : Row d → Fin r → Fin r → Fin r, (∀ x, IsLatin r (L x)) ∧
      Set.range (fun u => Set.range (internal u)) =
        Set.range (fun u => Set.range (latinPoint e L u)) := by
  classical
  have extra : AllowsExtra (Sum.elim mixed internal) := by
    by_contra h
    rw [potential_finrank_internal_triples _ hd family, ite_eq_right h] at dim
    omega
  have saturated := rowwise_slot_saturation e he mixed internal distinctRows extra count
  have red_eq : cyclicReduction (3 * r) =
      (ZMod.castHom (dvd_mul_right 3 r) (ZMod 3)).toAddMonoidHom := by
    unfold cyclicReduction
    rw [dite_eq_left (dvd_mul_right 3 r)]
  have chartInjective (u : U) :
      Function.Injective (fun j => (e (internal u 0).1 (internal u j).2).1) := by
    intro i j eq
    apply saturated u
    rw [red_eq]
    change ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) (internal u i).2 =
      ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) (internal u j).2
    simpa only [he] using eq
  have complete := rowwise_forced_pairs e he mixed internal distinctRows extra pairUnique
  obtain ⟨row, label, ranges, unique⟩ :=
    rowwise_residue_reordering e internal sameRow chartInjective complete
  let R (x : Row d) (a b c : Fin r) :=
    ∃ u, row u = x ∧ label u 0 = a ∧ label u 1 = b ∧ label u 2 = c
  have LExists (x : Row d) :
      ∃ L : Fin r → Fin r → Fin r, IsLatin r L ∧ ∀ a b c, R x a b c ↔ L a b = c := by
    obtain ⟨c01, c02, c12⟩ := latin_ordered_projection row label unique x
    exact (latin_of_projections (R x) c01 c02 c12).exists
  choose L hL using LExists
  refine ⟨L, fun x => (hL x).1, ?_⟩
  ext pts
  constructor
  · rintro ⟨u, rfl⟩
    have hval := ((hL (row u)).2 (label u 0) (label u 1) (label u 2)).mp
      ⟨u, rfl, rfl, rfl, rfl⟩
    refine ⟨(row u, label u 0, label u 1), ?_⟩
    change Set.range (latinPoint e L (row u, label u 0, label u 1)) = Set.range (internal u)
    rw [ranges u]
    congr 1
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact congrArg (fun c => (row u, (e (row u)).symm (ZMod.finEquiv 3 2, c))) hval
  · rintro ⟨⟨x, a, b⟩, rfl⟩
    obtain ⟨u, hrow, h0, h1, h2⟩ := ((hL x).2 a b (L x a b)).mpr rfl
    refine ⟨u, ?_⟩
    change Set.range (internal u) = Set.range (latinPoint e L (x, a, b))
    rw [ranges u]
    congr 1
    funext i
    fin_cases i
    · exact congrArg (fun p : Row d × Fin r =>
        (p.1, (e p.1).symm (ZMod.finEquiv 3 0, p.2))) (show (row u, label u 0) = (x, a) from Prod.ext hrow h0)
    · exact congrArg (fun p : Row d × Fin r =>
        (p.1, (e p.1).symm (ZMod.finEquiv 3 1, p.2))) (show (row u, label u 1) = (x, b) from Prod.ext hrow h1)
    · exact congrArg (fun p : Row d × Fin r =>
        (p.1, (e p.1).symm (ZMod.finEquiv 3 2, p.2))) (show (row u, label u 2) = (x, L x a b) from Prod.ext hrow h2)

/-- The unordered triple family determines the Latin-square assignment. -/
theorem latin_assignment_injective {d r : ℕ}
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    (L K : Row d → Fin r → Fin r → Fin r)
    (same : Set.range (fun u => Set.range (latinPoint e L u)) =
      Set.range (fun u => Set.range (latinPoint e K u))) : L = K := by
  funext x a b
  have h : Set.range (latinPoint e L (x,a,b)) ∈ Set.range
      (fun u => Set.range (latinPoint e K u)) :=
    same ▸ ⟨(x,a,b), rfl⟩
  obtain ⟨⟨y,c,d'⟩, graph⟩ := h
  have uniqueSlot (i : Fin 3) :
      latinPoint e L (x,a,b) i = latinPoint e K (y,c,d') i := by
    have hmem : latinPoint e L (x,a,b) i ∈ Set.range (latinPoint e K (y,c,d')) := by
      change Set.range (latinPoint e K (y,c,d')) = _ at graph
      rw [graph]
      exact ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := hmem
    have row : y = x := congrArg Prod.fst hj
    have heq := congrArg Prod.snd hj
    unfold latinPoint at heq
    change (e y).symm _ = (e x).symm _ at heq
    rw [row] at heq
    have ij : j = i := (ZMod.finEquiv 3).injective
      (congrArg Prod.fst ((e x).symm.injective heq))
    subst j
    exact hj.symm
  have row : x = y := congrArg Prod.fst (uniqueSlot 0)
  have labels (i : Fin 3) :=
    congrArg (fun z : Row d × ZMod (3 * r) => (e x z.2).2) (uniqueSlot i)
  subst y
  have ac : a = c := by simpa [latinPoint] using labels 0
  have bd : b = d' := by simpa [latinPoint] using labels 1
  have value : L x a b = K x c d' := by simpa [latinPoint] using labels 2
  simpa only [← ac, ← bd] using value

private def triple {r : ℕ} (L : Fin r → Fin r → Fin r) (p : Fin r × Fin r) : Fin 3 → Fin r :=
  Fin.cases p.1 (Fin.cases p.2 (fun _ => L p.1 p.2))

private theorem unique_01 {r : ℕ} (a b : Fin r) :
    ∃! p : Fin r × Fin r, p.1 = a ∧ p.2 = b := by
  exact ⟨(a, b), ⟨rfl, rfl⟩, fun _ h => Prod.ext h.1 h.2⟩

private theorem unique_02 {r : ℕ} {L : Fin r → Fin r → Fin r} (h : IsLatin r L)
    (a c : Fin r) : ∃! p : Fin r × Fin r, p.1 = a ∧ L p.1 p.2 = c := by
  obtain ⟨b, hb⟩ := (h.1 a).2 c
  refine ⟨(a, b), ⟨rfl, hb⟩, ?_⟩
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  change x = a at hx
  subst x
  exact Prod.ext rfl ((h.1 a).1 (hy.trans hb.symm))

private theorem unique_12 {r : ℕ} {L : Fin r → Fin r → Fin r} (h : IsLatin r L)
    (b c : Fin r) : ∃! p : Fin r × Fin r, p.2 = b ∧ L p.1 p.2 = c := by
  obtain ⟨a, ha⟩ := (h.2 b).2 c
  refine ⟨(a, b), ⟨rfl, ha⟩, ?_⟩
  rintro ⟨x, y⟩ ⟨hy, hx⟩
  change y = b at hy
  subst y
  exact Prod.ext ((h.2 b).1 (hx.trans ha.symm)) rfl

private theorem latin_slot_unique {r : ℕ} {L : Fin r → Fin r → Fin r} (h : IsLatin r L)
    (i j : Fin 3) (different : i ≠ j) (a b : Fin r) :
    ∃! p : Fin r × Fin r, triple L p i = a ∧ triple L p j = b := by
  fin_cases i <;> fin_cases j <;> try contradiction
  · exact unique_01 a b
  · exact unique_02 h a b
  · exact (existsUnique_congr (fun _ => and_comm)).mpr (unique_01 b a)
  · exact unique_12 h a b
  · exact (existsUnique_congr (fun _ => and_comm)).mpr (unique_02 h b a)
  · exact (existsUnique_congr (fun _ => and_comm)).mpr (unique_12 h b a)

/-- Rowwise Latin squares give a minimum extension with the extra dimension. -/
theorem optimal_family_of_latin {d r : ℕ} [NeZero (3 * r)] {T : Type*}
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    (he : ∀ x a, (e x a).1 = ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) a)
    (L : Row d → Fin r → Fin r → Fin r) (latin : ∀ x, IsLatin r (L x))
    (hd : 0 < d) (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (family : LiftedLineFamily mixed)
    (distinct_rows : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (pair_unique : ∀ t u x y, x ≠ y → covers (mixed t) x y → covers (mixed u) x y → t = u) :
    let U := Row d × (Fin r × Fin r)
    let internal := latinPoint e L
    (∀ u i, (internal u i).1 = u.1) ∧
    (∀ t, Function.Injective (Sum.elim mixed internal t)) ∧
    (∀ t u x y, x ≠ y → covers (Sum.elim mixed internal t) x y →
      covers (Sum.elim mixed internal u) x y → t = u) ∧
    LiftedLineFamily (Sum.elim mixed internal) ∧ AllowsExtra (Sum.elim mixed internal) ∧
    Module.finrank (ZMod 3) (potentialSpace (Sum.elim mixed internal) 0) = d + 1 ∧
    Nat.card U = 3 ^ d * r ^ 2 := by
  classical
  intro U internal
  let red := ZMod.castHom (dvd_mul_right 3 r) (ZMod 3)
  let row (x : Row d) (p : Fin r × Fin r) (i : Fin 3) := (internal (x,p) i).2
  have index (x : Row d) (p : Fin r × Fin r) (i : Fin 3) :
      e x (row x p i) = (ZMod.finEquiv 3 i, triple (L x) p i) := by
    change e x ((e x).symm (ZMod.finEquiv 3 i, ![p.1,p.2,L x p.1 p.2] i)) = _
    rw [Equiv.apply_symm_apply]
    fin_cases i <;> rfl
  have label (x : Row d) (p : Fin r × Fin r) (i : Fin 3) :
      red (row x p i) = ZMod.finEquiv 3 i := by
    rw [← he x, index]
  have hrow (x : Row d) (p : Fin r × Fin r) :
      Function.Injective (fun i => red (row x p i)) := by
    intro i j eq
    apply (ZMod.finEquiv 3).injective
    simpa only [label] using eq
  have hsums (x : Row d) (p : Fin r × Fin r) : (∑ i, red (row x p i)) = 0 := by
    simp_rw [label]
    rw [Fin.sum_univ_three]
    decide
  have hcover (x : Row d) (a b : ZMod (3 * r)) (different : red a ≠ red b) :
      ∃! p, covers (row x p) a b := by
    let i := (ZMod.finEquiv 3).symm (red a)
    let j := (ZMod.finEquiv 3).symm (red b)
    have ij : i ≠ j := (ZMod.finEquiv 3).symm.injective.ne different
    obtain ⟨p, hp, unique⟩ := latin_slot_unique (latin x) i j ij (e x a).2 (e x b).2
    have out (p' : Fin r × Fin r) (y : ZMod (3 * r)) :
        row x p' ((ZMod.finEquiv 3).symm (red y)) = y ↔
          triple (L x) p' ((ZMod.finEquiv 3).symm (red y)) = (e x y).2 := by
      constructor
      · intro eq
        have h := index x p' ((ZMod.finEquiv 3).symm (red y))
        rw [eq] at h
        exact (congrArg Prod.snd h).symm
      · intro eq
        apply (e x).injective
        rw [index, eq, (ZMod.finEquiv 3).apply_symm_apply]
        exact Prod.ext (he x y).symm rfl
    refine ⟨p, ⟨i,j,(out p a).mpr hp.1,(out p b).mpr hp.2⟩, ?_⟩
    rintro q ⟨k,l,hk,hl⟩
    have ki : k = i := by
      apply (ZMod.finEquiv 3).injective
      rw [(ZMod.finEquiv 3).apply_symm_apply,← label x q k,hk]
    have lj : l = j := by
      apply (ZMod.finEquiv 3).injective
      rw [(ZMod.finEquiv 3).apply_symm_apply,← label x q l,hl]
    subst k
    subst l
    exact unique q ⟨(out q a).mp hk, (out q b).mp hl⟩
  let combined := Sum.elim mixed internal
  have crosses (t : T) (x y : Row d × ZMod (3 * r)) (hne : x ≠ y)
      (h : covers (mixed t) x y) : x.1 ≠ y.1 := by
    obtain ⟨i,j,hi,hj⟩ := h
    have ij : i ≠ j := fun eq => hne (hi.symm.trans (eq ▸ hj))
    rw [← hi,← hj]
    exact (distinct_rows t).ne ij
  have within (t : U) (x y : Row d × ZMod (3 * r))
      (h : covers (internal t) x y) : x.1 = t.1 ∧ y.1 = t.1 := by
    obtain ⟨i,j,hi,hj⟩ := h
    exact ⟨congrArg Prod.fst hi.symm,congrArg Prod.fst hj.symm⟩
  have indexed (t : U) (x y : Row d × ZMod (3 * r))
      (h : covers (internal t) x y) : covers (row t.1 t.2) x.2 y.2 := by
    obtain ⟨i,j,hi,hj⟩ := h
    exact ⟨i,j,congrArg Prod.snd hi,congrArg Prod.snd hj⟩
  have injective : ∀ t, Function.Injective (combined t) := by
    intro t i j h
    cases t with
    | inl t => exact distinct_rows t (congrArg Prod.fst h)
    | inr t => exact hrow t.1 t.2 (congrArg (fun x => red x.2) h)
  have pairUnique : ∀ t u x y, x ≠ y → covers (combined t) x y →
      covers (combined u) x y → t = u := by
    intro t u x y hne ht hu
    cases t with
    | inl t =>
      cases u with
      | inl u => exact congrArg Sum.inl (pair_unique t u x y hne ht hu)
      | inr u =>
        obtain ⟨hx,hy⟩ := within u x y hu
        exact False.elim (crosses t x y hne ht (hx.trans hy.symm))
    | inr t =>
      cases u with
      | inl u =>
        obtain ⟨hx,hy⟩ := within t x y ht
        exact False.elim (crosses u x y hne hu (hx.trans hy.symm))
      | inr u =>
        have dx : red x.2 ≠ red y.2 := by
          obtain ⟨i,j,hi,hj⟩ := ht
          have ij : i ≠ j := fun eq => hne (hi.symm.trans (eq ▸ hj))
          rw [← hi,← hj]
          exact (hrow t.1 t.2).ne ij
        obtain ⟨a,_,ua⟩ := hcover x.1 x.2 y.2 dx
        apply congrArg Sum.inr
        have xt := (within t x y ht).1
        have xu := (within u x y hu).1
        have ht' := indexed t x y ht
        have hu' := indexed u x y hu
        rw [← xt] at ht'
        rw [← xu] at hu'
        exact Prod.ext (xt.symm.trans xu)
          ((ua t.2 ht').trans (ua u.2 hu').symm)
  have hfamily : LiftedLineFamily combined := by
    constructor
    · intro x y a b h
      obtain ⟨t,i,j,k,hij,hki,hkj,hi,hj,hk⟩ := family.1 x y a b h
      exact ⟨Sum.inl t,i,j,k,hij,hki,hkj,hi,hj,hk⟩
    · intro t
      cases t with
      | inl t => exact family.2 t
      | inr t => exact Or.inl (fun _ => rfl)
  have red_eq : cyclicReduction (3 * r) = red.toAddMonoidHom := by
    unfold cyclicReduction
    rw [dite_eq_left (dvd_mul_right 3 r)]
  have extra : AllowsExtra combined := by
    refine ⟨dvd_mul_right 3 r,?_⟩
    rw [red_eq]
    constructor
    · intro x a b missing
      have e : red a = red b := by
        by_contra h
        obtain ⟨c,⟨i,j,hi,hj⟩,_⟩ := hcover x a b h
        exact missing ⟨Sum.inr (x,c),i,j,Prod.ext rfl hi,Prod.ext rfl hj⟩
      change red (a-b) = 0
      rw [map_sub,e,sub_self]
    · intro t same
      cases t with
      | inl t =>
        have h : (mixed t 1).1 = (mixed t 0).1 := same 1
        exact False.elim ((by decide : (1 : Fin 3) ≠ 0) (distinct_rows t h))
      | inr t =>
        change red (∑ j, row t.1 t.2 j) = 0
        rw [map_sum]
        exact hsums t.1 t.2
  have dim := potential_finrank_internal_triples combined hd hfamily
  rw [ite_eq_left extra] at dim
  refine ⟨fun _ _ => rfl,injective,pairUnique,hfamily,extra,dim,?_⟩
  simp [U, Nat.card_eq_fintype_card, Fintype.card_prod, Row, ZMod.card, pow_two]

end D5.S3.Combinatorics.Matroids.RankThreeOptimalInternalLatin
