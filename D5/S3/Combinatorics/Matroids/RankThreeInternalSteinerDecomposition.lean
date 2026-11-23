/- GID: D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Internal triples of three distinct residues retain the extra ternary potential dimension. -/

import D5.S3.Combinatorics.Matroids.RankThreeOptimalInternalLatin
/-! The transversal part of an internal extension preserves the extra potential dimension. -/

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
    (dim : Module.finrank (ZMod 3) (potentialSpace (Sum.elim mixed internal) 0) = d+1) :
    let reduce := cyclicReduction (3 * r)
    (∀ u, Function.Injective (fun i => reduce (internal u i).2) ∨
      ∀ i, reduce (internal u i).2 = reduce (internal u 0).2) ∧
    (∀ (x : Row d) (a b : ZMod (3*r)), reduce a ≠ reduce b →
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
theorem transversal_finrank {d r : ℕ} {T U : Type*} [NeZero (3 * r)]
    (hd : 0 < d) (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (internal : U → Fin 3 → Row d × ZMod (3 * r))
    (family : LiftedLineFamily mixed)
    (crosses : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (sameRow : ∀ u i, (internal u i).1 = (internal u 0).1)
    (dim : Module.finrank (ZMod 3) (potentialSpace (Sum.elim mixed internal) 0) = d+1) :
    let reduce := cyclicReduction (3 * r)
    let Transversal := {u : U // Function.Injective (fun i => reduce (internal u i).2)}
    let kept := fun (u : Transversal) => internal u.val
    Module.finrank (ZMod 3) (potentialSpace (Sum.elim mixed kept) 0) = d+1 := by
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
    (dim : Module.finrank (ZMod 3) (potentialSpace (Sum.elim mixed internal) 0) = d+1) :
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
      have pointRed (a : ZMod (3*r)) : cyclicReduction (3*r) a = red a :=
        congrArg (fun f : ZMod (3*r) →+ ZMod 3 => f a) reduction_eq
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
theorem transversal_part_latin {d r : ℕ} {T : Type*} {U : Type u} [NeZero (3 * r)] [Fintype U]
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
theorem monochromatic_partial_steiner {d r : ℕ} {U : Type*}
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

end D5.S3.Combinatorics.Matroids.RankThreeInternalSteinerDecomposition
