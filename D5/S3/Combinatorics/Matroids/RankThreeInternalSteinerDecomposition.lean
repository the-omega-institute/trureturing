/- GID: D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Internal extensions with the extra ternary potential dimension split into rowwise Latin squares and partial Steiner systems. -/

import D5.S3.Combinatorics.Matroids.RankThreeOptimalInternalLatin
/-! The Latin and partial Steiner decomposition of ternary internal extensions. -/

namespace D5.S3.Combinatorics.Matroids.RankThreeInternalSteinerDecomposition

open D5.S3.Combinatorics.Matroids.RankThreeInternalTriplePotentials
open D5.S3.Combinatorics.Matroids.RankThreeOmissionPotentialFibers (potentialSpace)
open D5.S3.Combinatorics.Matroids.RankThreeOmissionPotentials (covers)

open RankThreeOptimalInternalLatin (latinPoint exists_latin_of_optimal_family)
open D5.S3.Combinatorics.LatinEulerianMultiples (IsLatin)

private theorem residue_dichotomy {d r : ℕ} {T U : Type*} [NeZero (3 * r)]
    (hd : 0 < d)
    (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (internal : U → Fin 3 → Row d × ZMod (3 * r))
    (family : LiftedLineFamily (Sum.elim mixed internal))
    (crosses : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (sameRow : ∀ u i, (internal u i).1 = (internal u 0).1)
    (dim : Module.finrank (ZMod 3) (potentialSpace (Sum.elim mixed internal) 0) = d + 1) :
    let reduce := cyclicReduction (3 * r)
    (∀ u, Function.Injective (fun i => reduce (internal u i).2) ∨
      ∀ i, reduce (internal u i).2 = reduce (internal u 0).2) ∧
    (∀ (x : Row d) (a b : ZMod (3 * r)), reduce a ≠ reduce b →
      ∃ u, covers (internal u) (x,a) (x,b)) := by
  classical
  intro reduce
  have extra : AllowsExtra (Sum.elim mixed internal) := by
    by_contra h
    rw [potential_finrank_internal_triples _ hd family, ite_eq_right h] at dim
    omega
  constructor
  · intro u
    have law : ∀ f : Fin 3 → ZMod 3, (∑ i, f i) = 0 →
        Function.Injective f ∨ ∀ i, f i = f 0 := by decide
    apply law
    rw [← map_sum]
    exact extra.2.2 (Sum.inr u) (sameRow u)
  · intro x a b different
    have covered : ∃ t, covers (Sum.elim mixed internal t) (x,a) (x,b) := by
      by_contra missing
      have zero := extra.2.1 x a b missing
      change reduce (a-b) = 0 at zero
      exact different (sub_eq_zero.mp ((map_sub reduce a b).symm.trans zero))
    obtain ⟨t, ht⟩ := covered
    cases t with
    | inr u => exact ⟨u,ht⟩
    | inl t =>
      obtain ⟨i,j,hi,hj⟩ := ht
      have eq := crosses t ((congrArg Prod.fst hi).trans (congrArg Prod.fst hj).symm)
      subst j
      exact (different (congrArg (fun p => reduce p.2) (hi.symm.trans hj))).elim

/-- Keeping only triples that meet every residue class preserves the extra dimension. -/
private theorem transversal_finrank {d r : ℕ} {T U : Type*} [NeZero (3 * r)]
    (hd : 0 < d) (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (internal : U → Fin 3 → Row d × ZMod (3 * r))
    (family : LiftedLineFamily mixed)
    (crosses : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (sameRow : ∀ u i, (internal u i).1 = (internal u 0).1)
    (dim : Module.finrank (ZMod 3) (potentialSpace (Sum.elim mixed internal) 0) = d + 1) :
    let reduce := cyclicReduction (3 * r)
    let Transversal := {u : U // Function.Injective (fun i => reduce (internal u i).2)}
    let kept := fun (u : Transversal) => internal u.val
    Module.finrank (ZMod 3) (potentialSpace (Sum.elim mixed kept) 0) = d + 1 := by
  classical
  intro reduce Transversal kept
  have combined : LiftedLineFamily (Sum.elim mixed internal) := by
    constructor
    · intro x y a b different
      obtain ⟨t,i,j,k,hij,hki,hkj,hi,hj,hk⟩ := family.1 x y a b different
      exact ⟨Sum.inl t,i,j,k,hij,hki,hkj,hi,hj,hk⟩
    · intro t
      cases t with
      | inl t => exact family.2 t
      | inr u => exact Or.inl (sameRow u)
  have extra : AllowsExtra (Sum.elim mixed internal) := by
    by_contra h
    rw [potential_finrank_internal_triples _ hd combined, ite_eq_right h] at dim
    omega
  obtain ⟨shape, coverage⟩ := residue_dichotomy hd mixed internal combined crosses sameRow dim
  have hFamily : LiftedLineFamily (Sum.elim mixed kept) := by
    constructor
    · intro x y a b different
      obtain ⟨t,i,j,k,hij,hki,hkj,hi,hj,hk⟩ := family.1 x y a b different
      exact ⟨Sum.inl t,i,j,k,hij,hki,hkj,hi,hj,hk⟩
    · intro t
      cases t with
      | inl t => exact family.2 t
      | inr u => exact Or.inl (sameRow u.val)
  have hExtra : AllowsExtra (Sum.elim mixed kept) := by
    refine ⟨extra.1, ?_, ?_⟩
    · intro x a b missing
      have eq : reduce a = reduce b := by
        by_contra h
        obtain ⟨u,i,j,hi,hj⟩ := coverage x a b h
        have trans : Function.Injective (fun i => reduce (internal u i).2) := by
          rcases shape u with trans | mono
          · exact trans
          · exfalso
            apply h
            exact (congrArg (fun z => reduce z.2) hi).symm.trans
              (((mono i).trans (mono j).symm).trans (congrArg (fun z => reduce z.2) hj))
        exact missing ⟨Sum.inr ⟨u,trans⟩,i,j,hi,hj⟩
      change reduce (a-b) = 0
      rw [map_sub, eq, sub_self]
    · intro t same
      cases t with
      | inl t => exact extra.2.2 (Sum.inl t) same
      | inr u => exact extra.2.2 (Sum.inr u.val) same
  simpa only [ite_eq_left hExtra] using potential_finrank_internal_triples _ hd hFamily

private theorem transversal_card {d r : ℕ} {T U : Type*} [NeZero (3 * r)] [Fintype U]
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    (he : ∀ x a, (e x a).1 = ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) a)
    (hd : 0 < d) (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (internal : U → Fin 3 → Row d × ZMod (3 * r))
    (family : LiftedLineFamily (Sum.elim mixed internal))
    (crosses : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (sameRow : ∀ u i, (internal u i).1 = (internal u 0).1)
    (unique : ∀ t u x y, x ≠ y → covers (internal t) x y → covers (internal u) x y → t = u)
    (dim : Module.finrank (ZMod 3) (potentialSpace (Sum.elim mixed internal) 0) = d + 1) :
    Nat.card {u : U // Function.Injective (fun i => cyclicReduction (3 * r) (internal u i).2)}
      = 3 ^ d * r ^ 2 := by
  classical
  let red := ZMod.castHom (dvd_mul_right 3 r) (ZMod 3)
  let V := {u : U // Function.Injective (fun i => cyclicReduction (3 * r) (internal u i).2)}
  change Nat.card V = _
  have reduction_eq : cyclicReduction (3 * r) = red.toAddMonoidHom := by
    unfold cyclicReduction
    rw [dite_eq_left (dvd_mul_right 3 r)]
  obtain ⟨shape, coverage⟩ := residue_dichotomy hd mixed internal family crosses sameRow dim
  let row (u : U) := (internal u 0).1
  let res (u : V) (i : Fin 3) := (e (row u.val) (internal u.val i).2).1
  have label_eq (u : V) (i : Fin 3) : res u i = red (internal u.val i).2 := he _ _
  have bij (u : V) : Function.Bijective (res u) := by
    let permutation := fun i => (ZMod.finEquiv 3).symm (res u i)
    have permInj : Function.Injective permutation := by
      intro i j h
      have eq : res u i = res u j := (ZMod.finEquiv 3).symm.injective h
      apply u.prop
      have pointRed (a : ZMod (3 * r)) : cyclicReduction (3 * r) a = red a :=
        congrArg (fun f : ZMod (3 * r) →+ ZMod 3 => f a) reduction_eq
      exact (pointRed _).trans (((label_eq u i).symm.trans (eq.trans (label_eq u j))).trans (pointRed _).symm)
    have hp := Finite.injective_iff_bijective.mp permInj
    exact (ZMod.finEquiv 3).bijective.comp hp
  let reorder (u : V) := Equiv.ofBijective (res u) (bij u)
  let point (x : Row d) (c : ZMod 3) (k : Fin r) := (x, (e x).symm (c,k))
  let cell (u : V) (c : ZMod 3) := (e (row u.val) (internal u.val ((reorder u).symm c)).2).2
  let code (u : V) := (row u.val, cell u 0, cell u 1)
  have pointEq (u : V) (c : ZMod 3) :
      internal u.val ((reorder u).symm c) = point (row u.val) c (cell u c) := by
    refine Prod.ext (sameRow u.val _) ?_
    change (internal u.val ((reorder u).symm c)).2 =
      (e (row u.val)).symm (c, cell u c)
    apply (e (row u.val)).injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext ((reorder u).apply_symm_apply c) rfl
  have diffPoint (x : Row d) (a b : Fin r) : point x 0 a ≠ point x 1 b := by
    intro eq
    have value : (e x).symm (0,a) = (e x).symm (1,b) := congrArg Prod.snd eq
    have bad : (0 : ZMod 3) = 1 := congrArg Prod.fst ((e x).symm.injective value)
    exact zero_ne_one bad
  have codeInj : Function.Injective code := by
    intro u v eq
    have erow : row u.val = row v.val := congrArg (fun (p : Row d × Fin r × Fin r) => p.1) eq
    have ea : cell u 0 = cell v 0 := congrArg (fun p => p.2.1) eq
    have eb : cell u 1 = cell v 1 := congrArg (fun p => p.2.2) eq
    apply Subtype.ext
    apply unique u.val v.val (point (row u.val) 0 (cell u 0)) (point (row u.val) 1 (cell u 1))
      (diffPoint _ _ _)
    · exact ⟨_,_,pointEq u 0,pointEq u 1⟩
    · exact ⟨_,_,by rw [pointEq, ← erow, ← ea],by rw [pointEq, ← erow, ← eb]⟩
  have codeOnto : Function.Surjective code := by
    rintro ⟨x,a,b⟩
    have ha : red ((e x).symm (0,a)) = 0 := by rw [← he x, Equiv.apply_symm_apply]
    have hb : red ((e x).symm (1,b)) = 1 := by rw [← he x, Equiv.apply_symm_apply]
    obtain ⟨u,i,j,hi,hj⟩ := coverage x ((e x).symm (0,a)) ((e x).symm (1,b)) (by
      rw [reduction_eq]
      change red ((e x).symm (0,a)) ≠ red ((e x).symm (1,b))
      rw [ha,hb]
      exact zero_ne_one)
    have hrow : row u = x := (sameRow u i).symm.trans (congrArg Prod.fst hi)
    have code_eq (k : Fin 3) (c : ZMod 3) (l : Fin r)
        (p : internal u k = point x c l) :
        e (row u) (internal u k).2 = (c,l) := by
      rw [p,hrow]
      exact (e x).apply_symm_apply _
    rcases shape u with injective | mono
    · let v : V := ⟨u,injective⟩
      have slot (k : Fin 3) (c : ZMod 3) (l : Fin r) (p : internal u k = point x c l) :
          cell v c = l := by
        have val := code_eq k c l p
        have slot_eq : (reorder v).symm c = k :=
          (reorder v).symm_apply_eq.mpr (congrArg Prod.fst val).symm
        change (e (row u) (internal u ((reorder v).symm c)).2).2 = l
        rw [slot_eq]
        exact congrArg Prod.snd val
      exact ⟨v,Prod.ext hrow (Prod.ext (slot i 0 a hi) (slot j 1 b hj))⟩
    · have bad := (mono i).trans (mono j).symm
      rw [reduction_eq] at bad
      change red (internal u i).2 = red (internal u j).2 at bad
      rw [hi,hj] at bad
      change red ((e x).symm (0,a)) = red ((e x).symm (1,b)) at bad
      rw [ha,hb] at bad
      exact (zero_ne_one bad).elim
  rw [Nat.card_congr (Equiv.ofBijective code ⟨codeInj,codeOnto⟩)]
  simp [Nat.card_eq_fintype_card, Fintype.card_prod, Row, ZMod.card, pow_two]

universe u

/-- The different-residue triples form the full Latin part of an extension. -/
private theorem transversal_part_latin {d r : ℕ} {T : Type*} {U : Type u} [NeZero (3 * r)] [Fintype U]
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    (he : ∀ x a, (e x a).1 = ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) a)
    (hd : 0 < d) (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (internal : U → Fin 3 → Row d × ZMod (3 * r))
    (family : LiftedLineFamily mixed)
    (crosses : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (sameRow : ∀ u i, (internal u i).1 = (internal u 0).1)
    (pairUnique : ∀ t u x y, x ≠ y → covers (Sum.elim mixed internal t) x y →
      covers (Sum.elim mixed internal u) x y → t = u)
    (dim : Module.finrank (ZMod 3) (potentialSpace (Sum.elim mixed internal) 0) = d + 1) :
    let V := {u : U // Function.Injective (fun i => cyclicReduction (3 * r) (internal u i).2)}
    ∃ L : Row d → Fin r → Fin r → Fin r, (∀ x, IsLatin r (L x)) ∧
      Set.range (fun u : V => Set.range (internal u.val)) =
        Set.range (fun u => Set.range (latinPoint e L u)) := by
  classical
  intro V
  let kept (u : V) := internal u.val
  have join (W : Type u) (f : W → U) : LiftedLineFamily (Sum.elim mixed (fun w => internal (f w))) := by
    constructor
    · intro x y a b different
      obtain ⟨t,i,j,k,hij,hki,hkj,hi,hj,hk⟩ := family.1 x y a b different
      exact ⟨Sum.inl t,i,j,k,hij,hki,hkj,hi,hj,hk⟩
    · intro t
      cases t with
      | inl t => exact family.2 t
      | inr t => exact Or.inl (sameRow (f t))
  have unique : ∀ t u x y, x ≠ y → covers (internal t) x y → covers (internal u) x y → t = u :=
    fun t u x y ne ht hu => Sum.inr.inj (pairUnique (Sum.inr t) (Sum.inr u) x y ne ht hu)
  have eCount := transversal_card e he hd mixed internal (join U id) crosses sameRow unique dim
  have count : Fintype.card V = 3 ^ d * r ^ 2 := by simpa only [Nat.card_eq_fintype_card] using eCount
  have keptUnique : ∀ t u x y, x ≠ y → covers (Sum.elim mixed kept t) x y →
      covers (Sum.elim mixed kept u) x y → t = u := by
    let embed : T ⊕ V → T ⊕ U := Sum.map id Subtype.val
    have inj : Function.Injective embed := Function.Injective.sumMap Function.injective_id Subtype.val_injective
    have points (t : T ⊕ V) : Sum.elim mixed kept t = Sum.elim mixed internal (embed t) := by
      cases t <;> rfl
    intro t u x y ne ht hu
    rw [points] at ht hu
    exact inj (pairUnique (embed t) (embed u) x y ne ht hu)
  exact exists_latin_of_optimal_family e he hd mixed kept (join V Subtype.val) crosses
    (fun u => sameRow u.val) keptUnique
    (transversal_finrank hd mixed internal family crosses sameRow dim) count


/-- A partial Steiner triple system on the labels, represented by unordered triples. -/
def IsPartialSteiner {r : ℕ} (family : Set (Set (Fin r))) : Prop :=
  (∀ s ∈ family, s.ncard = 3) ∧
  (∀ s ∈ family, ∀ t ∈ family, ∀ a b, a ≠ b → a ∈ s → b ∈ s → a ∈ t → b ∈ t → s = t)

/-- Within a fixed row and residue, the label triples form a partial Steiner system. -/
private theorem monochromatic_partial_steiner {d r : ℕ} {U : Type*}
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    (internal : U → Fin 3 → Row d × ZMod (3 * r))
    (sameRow : ∀ u i, (internal u i).1 = (internal u 0).1)
    (injective : ∀ u, Function.Injective (internal u))
    (pairUnique : ∀ t u x y, x ≠ y → covers (internal t) x y → covers (internal u) x y → t = u)
    (x : Row d) (c : ZMod 3) :
    let families : Set (Set (Fin r)) := {s | ∃ u, (internal u 0).1 = x ∧
      (∀ i, (e x (internal u i).2).1 = c) ∧
      s = Set.range (fun i => (e x (internal u i).2).2)}
    IsPartialSteiner families := by
  intro families
  let point (a : Fin r) := (x, (e x).symm (c,a))
  let label (u : U) (i : Fin 3) := (e x (internal u i).2).2
  have recover (u : U) (hx : (internal u 0).1 = x)
      (hc : ∀ i, (e x (internal u i).2).1 = c) (i : Fin 3) :
      internal u i = point (label u i) := by
    refine Prod.ext ((sameRow u i).trans hx) ?_
    change (internal u i).2 = (e x).symm (c, label u i)
    apply (e x).injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext (hc i) rfl
  have pointInj : Function.Injective point := by
    intro a b h
    have eq : (e x).symm (c,a) = (e x).symm (c,b) := congrArg Prod.snd h
    exact congrArg Prod.snd ((e x).symm.injective eq)
  constructor
  · rintro s ⟨u,hx,hc,rfl⟩
    have labelInj : Function.Injective (label u) := by
      intro i j eq
      apply injective u
      exact (recover u hx hc i).trans ((congrArg point eq).trans (recover u hx hc j).symm)
    change (Set.range (label u)).ncard = 3
    rw [Set.ncard_range_of_injective labelInj, Nat.card_fin]
  · rintro s ⟨u,hx,hc,rfl⟩ t ⟨v,hy,hd,rfl⟩ a b ne ⟨i,hi⟩ ⟨j,hj⟩ ⟨k,hk⟩ ⟨l,hl⟩
    have cover (w : U) (hr : (internal w 0).1 = x)
        (hc : ∀ i, (e x (internal w i).2).1 = c) (i j : Fin 3)
        (h1 : label w i = a) (h2 : label w j = b) :
        covers (internal w) (point a) (point b) :=
      ⟨i,j,(recover w hr hc i).trans (congrArg point h1),
        (recover w hr hc j).trans (congrArg point h2)⟩
    have uv := pairUnique u v (point a) (point b) (pointInj.ne ne)
      (cover u hx hc i j hi hj) (cover v hy hd k l hk hl)
    subst v
    rfl

/-- An extension with the extra dimension consists of the Latin part and a
partial Steiner system in every actual row and residue class. -/
theorem forward_decomposition {d r : ℕ} {T U : Type*} [NeZero (3 * r)] [Fintype U]
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    (he : ∀ x a, (e x a).1 = ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) a)
    (hd : 0 < d) (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (internal : U → Fin 3 → Row d × ZMod (3 * r))
    (family : LiftedLineFamily mixed)
    (crosses : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (sameRow : ∀ u i, (internal u i).1 = (internal u 0).1)
    (injective : ∀ u, Function.Injective (internal u))
    (pairUnique : ∀ t u x y, x ≠ y → covers (Sum.elim mixed internal t) x y →
      covers (Sum.elim mixed internal u) x y → t = u)
    (dim : Module.finrank (ZMod 3) (potentialSpace (Sum.elim mixed internal) 0) = d + 1) :
    ∃ (L : Row d → Fin r → Fin r → Fin r) (P : Row d → ZMod 3 → Set (Set (Fin r))),
      (∀ x, IsLatin r (L x)) ∧ (∀ x c, IsPartialSteiner (P x c)) ∧
      Set.range (fun u => Set.range (internal u)) =
        Set.range (fun u => Set.range (latinPoint e L u)) ∪
          {t | ∃ x c s, s ∈ P x c ∧ t = (fun a => (x, (e x).symm (c, a))) '' s} := by
  classical
  let reduce := cyclicReduction (3 * r)
  let point (x : Row d) (c : ZMod 3) (a : Fin r) := (x, (e x).symm (c,a))
  let label (x : Row d) (u : U) (i : Fin 3) := (e x (internal u i).2).2
  let blocks (x : Row d) (c : ZMod 3) : Set (Set (Fin r)) :=
    {s | ∃ u, (internal u 0).1 = x ∧ (∀ i, (e x (internal u i).2).1 = c) ∧
      s = Set.range (label x u)}
  obtain ⟨L, hLatin, hL⟩ :=
    transversal_part_latin e he hd mixed internal family crosses sameRow pairUnique dim
  have internalUnique : ∀ t u x y, x ≠ y → covers (internal t) x y →
      covers (internal u) x y → t = u :=
    fun t u x y ne ht hu => Sum.inr.inj (pairUnique (Sum.inr t) (Sum.inr u) x y ne ht hu)
  have hblocks (x : Row d) (c : ZMod 3) : IsPartialSteiner (blocks x c) :=
    monochromatic_partial_steiner e internal sameRow injective internalUnique x c
  have combined : LiftedLineFamily (Sum.elim mixed internal) := by
    constructor
    · intro x y a b different
      obtain ⟨t,i,j,k,hij,hki,hkj,hi,hj,hk⟩ := family.1 x y a b different
      exact ⟨Sum.inl t,i,j,k,hij,hki,hkj,hi,hj,hk⟩
    · intro t
      cases t with
      | inl t => exact family.2 t
      | inr u => exact Or.inl (sameRow u)
  obtain ⟨shape, _⟩ := residue_dichotomy hd mixed internal combined crosses sameRow dim
  have red_eq : ∀ a, reduce a = ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) a := by
    intro a
    dsimp only [reduce, cyclicReduction]
    rw [dite_eq_left (dvd_mul_right 3 r)]
    rfl
  have recover (u : U) (x : Row d) (c : ZMod 3) (hx : (internal u 0).1 = x)
      (hc : ∀ i, (e x (internal u i).2).1 = c) :
      Set.range (internal u) = point x c '' Set.range (label x u) := by
    have pair (i : Fin 3) : internal u i = point x c (label x u i) := by
      refine Prod.ext ((sameRow u i).trans hx) ?_
      change (internal u i).2 = (e x).symm (c, label x u i)
      apply (e x).injective
      rw [Equiv.apply_symm_apply]
      exact Prod.ext (hc i) rfl
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨label x u i, ⟨i, rfl⟩, (pair i).symm⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, pair i⟩
  refine ⟨L, blocks, hLatin, hblocks, ?_⟩
  ext t
  constructor
  · rintro ⟨u,rfl⟩
    rcases shape u with trans | same
    · apply Or.inl
      rw [← hL]
      exact ⟨⟨u,trans⟩,rfl⟩
    · apply Or.inr
      let x := (internal u 0).1
      let c := reduce (internal u 0).2
      have hc (i : Fin 3) : (e x (internal u i).2).1 = c := by
        rw [he x, ← red_eq]
        exact same i
      exact ⟨x,c,Set.range (label x u),⟨u,rfl,hc,rfl⟩,recover u x c rfl hc⟩
  · rintro (h | ⟨x,c,s,⟨u,hx,hc,rfl⟩,eq⟩)
    · rw [← hL] at h
      obtain ⟨u,hu⟩ := h
      exact ⟨u.val,hu⟩
    · exact ⟨u,(recover u x c hx hc).trans eq.symm⟩

private theorem add_constant_residue_triples {d r : ℕ} [NeZero (3 * r)] {A B : Type*}
    (hd : 0 < d)
    (base : A → Fin 3 → Row d × ZMod (3 * r))
    (more : B → Fin 3 → Row d × ZMod (3 * r))
    (family : LiftedLineFamily base) (extra : AllowsExtra base)
    (sameRow : ∀ b i, (more b i).1 = (more b 0).1)
    (sameResidue : ∀ b i, cyclicReduction (3 * r) (more b i).2 =
      cyclicReduction (3 * r) (more b 0).2) :
    Module.finrank (ZMod 3) (potentialSpace (Sum.elim base more) 0) = d + 1 := by
  let joined := Sum.elim base more
  have lifted : LiftedLineFamily joined := by
    constructor
    · intro x y a b h
      obtain ⟨t,i,j,k,hij,hki,hkj,hi,hj,hk⟩ := family.1 x y a b h
      exact ⟨Sum.inl t,i,j,k,hij,hki,hkj,hi,hj,hk⟩
    · intro t
      cases t with
      | inl t => exact family.2 t
      | inr b => exact Or.inl (sameRow b)
  have compatible : AllowsExtra joined := by
    refine ⟨extra.1, ?_, ?_⟩
    · intro x a b absent
      exact extra.2.1 x a b (by
        rintro ⟨t, ht⟩
        exact absent ⟨Sum.inl t, ht⟩)
    · intro t h
      cases t with
      | inl a => exact extra.2.2 a h
      | inr b =>
        change cyclicReduction (3 * r) (∑ i, (more b i).2) = 0
        rw [map_sum]
        simp_rw [sameResidue b]
        rw [Fin.sum_univ_three]
        simpa only [three_nsmul, add_assoc] using
          ZModModule.char_nsmul_eq_zero 3 (cyclicReduction (3 * r) (more b 0).2)
  simpa only [ite_eq_left compatible] using potential_finrank_internal_triples joined hd lifted

private abbrev MonochromaticIndex {d r : ℕ}
    (P : Row d → ZMod 3 → Set (Set (Fin r))) :=
  {u : Row d × ZMod 3 × Set (Fin r) // u.2.2 ∈ P u.1 u.2.1}

private noncomputable def monoEnumeration {d r : ℕ}
    {P : Row d → ZMod 3 → Set (Set (Fin r))}
    (hP : ∀ x c, IsPartialSteiner (P x c)) (u : MonochromaticIndex P) :
    Fin 3 ≃ u.val.2.2 := by
  classical
  apply Equiv.symm
  apply Fintype.equivFinOfCardEq
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  exact (hP u.val.1 u.val.2.1).1 _ u.prop

private noncomputable def monoPoints {d r : ℕ}
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    {P : Row d → ZMod 3 → Set (Set (Fin r))}
    (hP : ∀ x c, IsPartialSteiner (P x c)) (u : MonochromaticIndex P) (i : Fin 3) :
    Row d × ZMod (3 * r) :=
  (u.val.1, (e u.val.1).symm (u.val.2.1, (monoEnumeration hP u i).val))

private theorem mono_range {d r : ℕ}
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    {P : Row d → ZMod 3 → Set (Set (Fin r))}
    (hP : ∀ x c, IsPartialSteiner (P x c)) (u : MonochromaticIndex P) :
    Set.range (monoPoints e hP u) =
      (fun a => (u.val.1, (e u.val.1).symm (u.val.2.1, a))) '' u.val.2.2 := by
  ext p
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨(monoEnumeration hP u i).val,(monoEnumeration hP u i).prop,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨i,hi⟩ := (monoEnumeration hP u).surjective ⟨a,ha⟩
    exact ⟨i,congrArg (fun v : u.val.2.2 => (u.val.1, (e u.val.1).symm (u.val.2.1,v.val))) hi⟩

private theorem mono_observations {d r : ℕ}
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    {P : Row d → ZMod 3 → Set (Set (Fin r))}
    (hP : ∀ x c, IsPartialSteiner (P x c)) (u : MonochromaticIndex P)
    (p : Row d × ZMod (3 * r)) (hp : p ∈ Set.range (monoPoints e hP u)) :
    p.1 = u.val.1 ∧ (e p.1 p.2).1 = u.val.2.1 ∧
      (e p.1 p.2).2 ∈ u.val.2.2 := by
  obtain ⟨i,rfl⟩ := hp
  change u.val.1 = u.val.1 ∧
    (e u.val.1 ((e u.val.1).symm (u.val.2.1,(monoEnumeration hP u i).val))).1 = u.val.2.1 ∧
    (e u.val.1 ((e u.val.1).symm (u.val.2.1,(monoEnumeration hP u i).val))).2 ∈ u.val.2.2
  rw [Equiv.apply_symm_apply]
  exact ⟨rfl,rfl,(monoEnumeration hP u i).prop⟩

private theorem mono_pair_unique {d r : ℕ}
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    {P : Row d → ZMod 3 → Set (Set (Fin r))}
    (hP : ∀ x c, IsPartialSteiner (P x c)) :
    ∀ u v x y, x ≠ y → covers (monoPoints e hP u) x y →
      covers (monoPoints e hP v) x y → u = v := by
  rintro ⟨⟨xu,cu,s⟩, hs⟩ ⟨⟨xv,cv,t⟩, ht⟩ x y neq ⟨i,j,hi,hj⟩ ⟨k,l,hk,hl⟩
  have oxu := mono_observations e hP _ x ⟨i,hi⟩
  have oyu := mono_observations e hP _ y ⟨j,hj⟩
  have oxv := mono_observations e hP _ x ⟨k,hk⟩
  have oyv := mono_observations e hP _ y ⟨l,hl⟩
  change x.1 = xu ∧ (e x.1 x.2).1 = cu ∧ (e x.1 x.2).2 ∈ s at oxu
  change y.1 = xu ∧ (e y.1 y.2).1 = cu ∧ (e y.1 y.2).2 ∈ s at oyu
  change x.1 = xv ∧ (e x.1 x.2).1 = cv ∧ (e x.1 x.2).2 ∈ t at oxv
  change y.1 = xv ∧ (e y.1 y.2).1 = cv ∧ (e y.1 y.2).2 ∈ t at oyv
  have rows := oxu.1.symm.trans oxv.1
  have residues := oxu.2.1.symm.trans oxv.2.1
  subst xv
  subst cv
  have rowxy := oxu.1.trans oyu.1.symm
  have labelxy : (e x.1 x.2).2 ≠ (e y.1 y.2).2 := by
    intro eq
    have residuesXY : (e x.1 x.2).1 = (e y.1 y.2).1 :=
      oxu.2.1.trans oyu.2.1.symm
    rw [← rowxy] at eq residuesXY
    exact neq (Prod.ext rowxy ((e x.1).injective (Prod.ext residuesXY eq)))
  have same := (hP xu cu).2 s hs t ht _ _ labelxy oxu.2.2 oyu.2.2 oxv.2.2 oyv.2.2
  subst t
  rfl

/-- Independently chosen same-residue partial Steiner systems can be added
to the Latin triples of every row. -/
theorem realize_decomposition {d r : ℕ} [NeZero (3 * r)] {T : Type*}
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    (he : ∀ x a, (e x a).1 = ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) a)
    (hd : 0 < d)
    (L : Row d → Fin r → Fin r → Fin r) (hL : ∀ x, IsLatin r (L x))
    (P : Row d → ZMod 3 → Set (Set (Fin r))) (hP : ∀ x c, IsPartialSteiner (P x c))
    (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (family : LiftedLineFamily mixed)
    (crosses : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (mixedUnique : ∀ t u x y, x ≠ y → covers (mixed t) x y → covers (mixed u) x y → t = u) :
    ∃ mono : MonochromaticIndex P → Fin 3 → Row d × ZMod (3 * r),
      let combined := Sum.elim (Sum.elim mixed (latinPoint e L)) mono
      (∀ u, Set.range (mono u) =
        (fun a => (u.val.1, (e u.val.1).symm (u.val.2.1, a))) '' u.val.2.2) ∧
      (∀ t, Function.Injective (combined t)) ∧
      (∀ t u x y, x ≠ y → covers (combined t) x y →
        covers (combined u) x y → t = u) ∧
      Module.finrank (ZMod 3) (potentialSpace combined 0) = d + 1 := by
  classical
  let base := Sum.elim mixed (latinPoint e L)
  let mono := monoPoints e hP
  let combined := Sum.elim base mono
  obtain ⟨_, baseInj, baseUnique, baseFamily, baseExtra, _, _⟩ :=
    RankThreeOptimalInternalLatin.optimal_family_of_latin e he L hL hd mixed family crosses mixedUnique
  have monoInj (u : MonochromaticIndex P) : Function.Injective (mono u) := by
    intro i j eq
    have val := congrArg Prod.snd eq
    change (e u.val.1).symm (u.val.2.1,(monoEnumeration hP u i).val) =
      (e u.val.1).symm (u.val.2.1,(monoEnumeration hP u j).val) at val
    apply (monoEnumeration hP u).injective
    exact Subtype.ext (congrArg Prod.snd ((e u.val.1).symm.injective val))
  have conflicting (t : T ⊕ (Row d × (Fin r × Fin r))) (u : MonochromaticIndex P)
      (x y : Row d × ZMod (3 * r)) (ne : x ≠ y)
      (ht : covers (base t) x y) (hu : covers (mono u) x y) : False := by
    obtain ⟨i,j,hi,hj⟩ := ht
    have ij : i ≠ j := fun eq => ne (hi.symm.trans (eq ▸ hj))
    obtain ⟨k,l,hk,hl⟩ := hu
    have ox := mono_observations e hP u x ⟨k,hk⟩
    have oy := mono_observations e hP u y ⟨l,hl⟩
    cases t with
    | inl t =>
      have same : (mixed t i).1 = (mixed t j).1 :=
        (congrArg Prod.fst hi).trans (ox.1.trans (oy.1.symm.trans (congrArg Prod.fst hj).symm))
      exact ij (crosses t same)
    | inr t =>
      have label (i : Fin 3) :
          (e (latinPoint e L t i).1 (latinPoint e L t i).2).1 = ZMod.finEquiv 3 i := by
        unfold latinPoint
        rw [Equiv.apply_symm_apply]
      change latinPoint e L t i = x at hi
      change latinPoint e L t j = y at hj
      have eq : (e x.1 x.2).1 = (e y.1 y.2).1 := ox.2.1.trans oy.2.1.symm
      rw [← hi, ← hj, label, label] at eq
      exact ij ((ZMod.finEquiv 3).injective eq)
  have sameResidue (u : MonochromaticIndex P) (i : Fin 3) :
      cyclicReduction (3 * r) (mono u i).2 = cyclicReduction (3 * r) (mono u 0).2 := by
    have eq : ∀ i, cyclicReduction (3 * r) (mono u i).2 = u.val.2.1 := by
      intro i
      unfold cyclicReduction
      rw [dite_eq_left (dvd_mul_right 3 r)]
      change ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) (mono u i).2 = u.val.2.1
      rw [← he u.val.1]
      exact (mono_observations e hP u (mono u i) ⟨i,rfl⟩).2.1
    exact (eq i).trans (eq 0).symm
  refine ⟨mono, mono_range e hP, ?_, ?_, ?_⟩
  · intro t
    cases t with
    | inl t => exact baseInj t
    | inr u => exact monoInj u
  · intro t u x y neq ht hu
    cases t with
    | inl t =>
      cases u with
      | inl u => exact congrArg Sum.inl (baseUnique t u x y neq ht hu)
      | inr u => exact (conflicting t u x y neq ht hu).elim
    | inr t =>
      cases u with
      | inl u => exact (conflicting u t x y neq hu ht).elim
      | inr u => exact congrArg Sum.inr (mono_pair_unique e hP t u x y neq ht hu)
  · exact add_constant_residue_triples hd base mono baseFamily baseExtra (fun _ _ => rfl) sameResidue

/-- The unordered family of internal triples from prescribed square and packing data. -/
def extendedFamily {d r : ℕ} (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    (L : Row d → Fin r → Fin r → Fin r) (P : Row d → ZMod 3 → Set (Set (Fin r))) :
    Set (Set (Row d × ZMod (3 * r))) :=
  Set.range (fun u => Set.range (latinPoint e L u)) ∪
    {t | ∃ x c s, s ∈ P x c ∧ t = (fun a => (x, (e x).symm (c, a))) '' s}

/-- The unordered family uniquely determines its square and packing data. -/
theorem decomposition_unique {d r : ℕ} (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    (L K : Row d → Fin r → Fin r → Fin r)
    (P Q : Row d → ZMod 3 → Set (Set (Fin r)))
    (hP : ∀ x c, IsPartialSteiner (P x c)) (hQ : ∀ x c, IsPartialSteiner (Q x c))
    (same : extendedFamily e L P = extendedFamily e K Q) : L = K ∧ P = Q := by
  let residue (p : Row d × ZMod (3 * r)) := (e p.1 p.2).1
  have slot (D : Row d → Fin r → Fin r → Fin r) (u : Row d × Fin r × Fin r) (i : Fin 3) :
      residue (latinPoint e D u i) = ZMod.finEquiv 3 i := by
    unfold residue latinPoint
    rw [Equiv.apply_symm_apply]
  have image_const (x : Row d) (c : ZMod 3) (S : Set (Fin r))
      (p : Row d × ZMod (3 * r)) (hp : p ∈ (fun a => (x, (e x).symm (c,a))) '' S) :
      p.1 = x ∧ residue p = c := by
    obtain ⟨a,_,rfl⟩ := hp
    change x = x ∧ (e x ((e x).symm (c,a))).1 = c
    rw [Equiv.apply_symm_apply]
    exact ⟨rfl,rfl⟩
  have disjoint (D : Row d → Fin r → Fin r → Fin r) (u : Row d × Fin r × Fin r)
      (x : Row d) (c : ZMod 3) (S : Set (Fin r)) :
      Set.range (latinPoint e D u) ≠ (fun a => (x, (e x).symm (c,a))) '' S := by
    intro eq
    have h0 : latinPoint e D u 0 ∈ (fun a => (x, (e x).symm (c,a))) '' S :=
      eq ▸ ⟨0,rfl⟩
    have h1 : latinPoint e D u 1 ∈ (fun a => (x, (e x).symm (c,a))) '' S :=
      eq ▸ ⟨1,rfl⟩
    have eqResidue := (image_const x c S _ h0).2.trans (image_const x c S _ h1).2.symm
    rw [slot,slot] at eqResidue
    exact (by decide : (0 : Fin 3) ≠ 1) ((ZMod.finEquiv 3).injective eqResidue)
  have latin_subset (D E : Row d → Fin r → Fin r → Fin r)
      (A B : Row d → ZMod 3 → Set (Set (Fin r)))
      (eq : extendedFamily e D A = extendedFamily e E B) :
      Set.range (fun u => Set.range (latinPoint e D u)) ⊆
      Set.range (fun u => Set.range (latinPoint e E u)) := by
    rintro s ⟨u,rfl⟩
    have hm : Set.range (latinPoint e D u) ∈ extendedFamily e E B :=
      eq ▸ (show Set.range (latinPoint e D u) ∈ extendedFamily e D A from Or.inl ⟨u,rfl⟩)
    rcases hm with h | ⟨x,c,t,_,heq⟩
    · exact h
    · exact (disjoint D u x c t heq).elim
  refine ⟨RankThreeOptimalInternalLatin.latin_assignment_injective e L K
    (Set.Subset.antisymm (latin_subset L K P Q same) (latin_subset K L Q P same.symm)), ?_⟩
  have mono_subset (D E : Row d → Fin r → Fin r → Fin r)
      (A B : Row d → ZMod 3 → Set (Set (Fin r)))
      (hA : ∀ x c, IsPartialSteiner (A x c))
      (eq : extendedFamily e D A = extendedFamily e E B) (x : Row d) (c : ZMod 3) :
      A x c ⊆ B x c := by
    intro s hs
    let point (a : Fin r) := (x, (e x).symm (c,a))
    have hm : point '' s ∈ extendedFamily e E B :=
      eq ▸ (show point '' s ∈ extendedFamily e D A from Or.inr ⟨x,c,s,hs,rfl⟩)
    rcases hm with ⟨u,hu⟩ | ⟨y,b,t,ht,heq⟩
    · exact (disjoint E u x c s hu).elim
    · let a := monoEnumeration hA ⟨(x,c,s),hs⟩ 0
      have hp : point a.val ∈ point '' s := ⟨a.val,a.prop,rfl⟩
      have obsA := image_const x c s (point a.val) hp
      have obsB := image_const y b t (point a.val) (heq ▸ hp)
      have hrow := obsA.1.symm.trans obsB.1
      have hres := obsA.2.symm.trans obsB.2
      subst y
      subst b
      have pi : Function.Injective point := by
        intro a b eq
        have h : (e x).symm (c,a) = (e x).symm (c,b) := congrArg Prod.snd eq
        exact congrArg Prod.snd ((e x).symm.injective h)
      change point '' s = point '' t at heq
      have sameSet : s = t := Set.image_injective.mpr pi heq
      exact sameSet ▸ ht
  funext x c
  exact Set.Subset.antisymm (mono_subset L K P Q hP same x c)
    (mono_subset K L Q P hQ same.symm x c)

end D5.S3.Combinatorics.Matroids.RankThreeInternalSteinerDecomposition
