/- GID: D5/S3/Combinatorics/Matroids/RankThreeMinimumInternalAdditions
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankThreeMinimumInternalAdditions
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Raising the ternary potential dimension requires a sharp number of internal triples. -/

import D5.S3.Combinatorics.Matroids.RankThreeInternalTriplePotentials
import D5.S3.Combinatorics.Matroids.RankThreeOmissionPairCount

namespace D5.S3.Combinatorics.Matroids.RankThreeMinimumInternalAdditions

open RankThreeInternalTriplePotentials (Row LiftedLineFamily AllowsExtra cyclicReduction potential_finrank_internal_triples)
open RankThreeOmissionPotentialFibers (potentialSpace point_potential_evaluations)
open RankThreeOmissionPairCount (potential_fiber_pair_count_le)
open RankThreeOmissionPotentials (covers)

/-- After the cyclic coefficient becomes available, the total mixed-pair
bound fixes the minimum number of additions to the original lifted lines. -/
theorem internal_additions_lower_bound {d r : ℕ} [NeZero (3*r)] {T U : Type*}
    [Fintype T] [Fintype U] (hd : 0 < d)
    (mixed : T → Fin 3 → Row d × ZMod (3*r))
    (internal : U → Fin 3 → Row d × ZMod (3*r))
    (family : LiftedLineFamily (Sum.elim mixed internal))
    (extra : AllowsExtra (Sum.elim mixed internal))
    (hinj : ∀ t, Function.Injective (Sum.elim mixed internal t))
    (hdis : ∀ t u x y, x ≠ y → covers (Sum.elim mixed internal t) x y →
      covers (Sum.elim mixed internal u) x y → t = u)
    (mixed_count : 6 * Fintype.card T = 3^d * (3^d-1) * (3*r)^2) :
    3^d * r^2 ≤ Fintype.card U := by
  classical
  let points := Sum.elim mixed internal
  let P := potentialSpace points 0
  let e := Module.finrank (ZMod 3) P
  let b := Module.finBasis (ZMod 3) P
  let s := Nat.card {x : Row d × ZMod (3*r) // (fun k => (b k).val x) = 0}
  have dim : e = d+1 := by
    dsimp only [e,P]
    rw [potential_finrank_internal_triples points hd family,ite_eq_left extra]
  have card (q : ℕ) [NeZero q] : Fintype.card (Row d × ZMod q) = 3^d * q := by
    simp [Row,Fintype.card_prod,ZMod.card]
  have count : Fintype.card (Row d × ZMod (3*r)) = 3^e * s :=
    (point_potential_evaluations points hinj hdis 0 b).2.2.1
  have size : s = r := by
    rw [card,dim,pow_succ] at count
    have eq : (3^d * 3) * r = (3^d * 3) * s := by simpa only [Nat.mul_assoc] using count
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) eq).symm
  have bound : 3^e * (3^e-1) * s^2 ≤ 6 * Fintype.card (T ⊕ U) :=
    potential_fiber_pair_count_le points 0 hinj hdis b
  rw [dim,size,pow_succ,Fintype.card_sum,Nat.mul_add,mixed_count] at bound
  let q := 3^d
  have pos : 0 < q := by positivity
  have pred : q * 3 - 1 = 3*(q-1) + 2 := by omega
  change q * 3 * (q * 3 - 1) * r^2 ≤ q * (q-1) * (3*r)^2 + 6 * Fintype.card U at bound
  have expand : q * 3 * (q * 3 - 1) * r^2 =
      q * (q-1) * (3*r)^2 + 6 * (q*r^2) := by
    conv_lhs => rw [pred]
    ring
  rw [expand] at bound
  change q * r^2 ≤ Fintype.card U
  omega

private theorem residue_indexing (r : ℕ) [NeZero (3*r)] :
    ∃ e : ZMod (3*r) ≃ ZMod 3 × Fin r,
      ∀ a, (e a).1 = ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) a := by
  let red := ZMod.castHom (dvd_mul_right 3 r) (ZMod 3)
  have bound (a : ZMod (3*r)) : a.val / 3 < r := by
    have h := a.val_lt
    omega
  have lifted (a : ZMod 3) (b : Fin r) : a.val + 3*b.val < 3*r := by
    have ha := a.val_lt
    have hb := b.isLt
    omega
  have red_val (a : ZMod (3*r)) : red a = (a.val : ZMod 3) :=
    (congrArg red (ZMod.natCast_zmod_val a).symm).trans (map_natCast red a.val)
  let forward (a : ZMod (3*r)) : ZMod 3 × Fin r := (red a, ⟨a.val/3,bound a⟩)
  let backward (p : ZMod 3 × Fin r) : ZMod (3*r) := (p.1.val + 3*p.2.val : ℕ)
  refine ⟨⟨forward,backward,?_,?_⟩, fun _ => rfl⟩
  · intro a
    apply ZMod.val_injective (3*r)
    change (((red a).val + 3*(a.val/3) : ℕ) : ZMod (3*r)).val = a.val
    rw [ZMod.val_natCast_of_lt (lifted (red a) ⟨a.val/3,bound a⟩)]
    rw [red_val,ZMod.val_natCast]
    exact Nat.mod_add_div _ _
  · rintro ⟨a,b⟩
    have hinv := (Nat.residueClassesEquiv 3).right_inv (a,b.val)
    apply Prod.ext
    · change red ((a.val + 3*b.val : ℕ) : ZMod (3*r)) = a
      rw [map_natCast]
      exact congrArg Prod.fst hinv
    · apply Fin.ext
      change (((a.val + 3*b.val : ℕ) : ZMod (3*r)).val / 3) = b.val
      rw [ZMod.val_natCast_of_lt (lifted a b)]
      exact congrArg Prod.snd hinv

private def transversal {r : ℕ} (c : ZMod r × ZMod r) (i : Fin 3) :
    ZMod 3 × ZMod r := ![(0,c.1),(1,c.2),(2,-(c.1+c.2))] i

private theorem transversal_label {r : ℕ} (c : ZMod r × ZMod r) (i : Fin 3) :
    (transversal c i).1 = ZMod.finEquiv 3 i := by
  fin_cases i <;> rfl

private theorem transversal_pair_exists {r : ℕ} (i j : Fin 3) (hne : i ≠ j)
    (a b : ZMod r) :
    ∃ c : ZMod r × ZMod r, (transversal c i).2 = a ∧ (transversal c j).2 = b := by
  fin_cases i <;> fin_cases j <;> try contradiction
  · exact ⟨(a,b),rfl,rfl⟩
  · exact ⟨(a,-(a+b)),rfl,by change -(a + -(a+b)) = b; abel⟩
  · exact ⟨(b,a),rfl,rfl⟩
  · exact ⟨(-(a+b),a),rfl,by change -(-(a+b) + a) = b; abel⟩
  · exact ⟨(b,-(a+b)),by change -(b + -(a+b)) = a; abel,rfl⟩
  · exact ⟨(-(a+b),b),by change -(-(a+b) + b) = a; abel,rfl⟩

private theorem transversal_pair_unique {r : ℕ} (i j : Fin 3) (hne : i ≠ j)
    {a b : ZMod r × ZMod r}
    (hi : (transversal a i).2 = (transversal b i).2)
    (hj : (transversal a j).2 = (transversal b j).2) : a = b := by
  fin_cases i <;> fin_cases j <;> try contradiction
  · exact Prod.ext hi hj
  · change a.1 = b.1 at hi
    change -(a.1 + a.2) = -(b.1 + b.2) at hj
    rw [neg_inj,hi] at hj
    exact Prod.ext hi (add_left_cancel hj)
  · exact Prod.ext hj hi
  · change a.2 = b.2 at hi
    change -(a.1 + a.2) = -(b.1 + b.2) at hj
    rw [neg_inj,hi] at hj
    exact Prod.ext (add_right_cancel hj) hi
  · change a.1 = b.1 at hj
    change -(a.1 + a.2) = -(b.1 + b.2) at hi
    rw [neg_inj,hj] at hi
    exact Prod.ext hj (add_left_cancel hi)
  · change a.2 = b.2 at hj
    change -(a.1 + a.2) = -(b.1 + b.2) at hi
    rw [neg_inj,hj] at hi
    exact Prod.ext (add_right_cancel hi) hj


private theorem residue_transversal (r : ℕ) [NeZero (3*r)] :
    let red := ZMod.castHom (dvd_mul_right 3 r) (ZMod 3)
    ∃ points : ZMod r × ZMod r → Fin 3 → ZMod (3*r),
      (∀ c, Function.Injective (fun i => red (points c i))) ∧
      (∀ c, (∑ i, red (points c i)) = 0) ∧
      ∀ a b, red a ≠ red b → ∃! c, covers (points c) a b := by
  classical
  intro red
  have : NeZero r := ⟨by
    intro hr
    exact NeZero.ne (3*r) (by simp [hr])⟩
  obtain ⟨e,he⟩ := residue_indexing r
  let E := e.trans (Equiv.prodCongr (Equiv.refl (ZMod 3)) (ZMod.finEquiv r).toEquiv)
  have first (a : ZMod (3*r)) : (E a).1 = red a := he a
  let points (c : ZMod r × ZMod r) (i : Fin 3) := E.symm (transversal c i)
  have indexed (c : ZMod r × ZMod r) (i : Fin 3) :
      E (points c i) = transversal c i := E.apply_symm_apply _
  have label (c : ZMod r × ZMod r) (i : Fin 3) :
      red (points c i) = ZMod.finEquiv 3 i := by
    rw [← first, indexed, transversal_label]
  refine ⟨points, ?_, ?_, ?_⟩
  · intro c i j h
    exact (ZMod.finEquiv 3).injective ((label c i).symm.trans (h.trans (label c j)))
  · intro c
    simp_rw [label]
    rw [Fin.sum_univ_three]
    decide
  · intro a b diff
    let i := (ZMod.finEquiv 3).symm (red a)
    let j := (ZMod.finEquiv 3).symm (red b)
    have ij : i ≠ j := (ZMod.finEquiv 3).symm.injective.ne diff
    obtain ⟨c,hc,hd⟩ := transversal_pair_exists i j ij (E a).2 (E b).2
    have point_a : points c i = a := by
      apply E.injective
      rw [indexed]
      exact Prod.ext ((transversal_label c i).trans (((ZMod.finEquiv 3).apply_symm_apply _).trans
        (first a).symm)) hc
    have point_b : points c j = b := by
      apply E.injective
      rw [indexed]
      exact Prod.ext ((transversal_label c j).trans (((ZMod.finEquiv 3).apply_symm_apply _).trans
        (first b).symm)) hd
    refine ⟨c,⟨i,j,point_a,point_b⟩,?_⟩
    rintro t ⟨k,l,hk,hl⟩
    have ki : k = i := by
      apply (ZMod.finEquiv 3).injective
      rw [(ZMod.finEquiv 3).apply_symm_apply,← label t k,hk]
    have lj : l = j := by
      apply (ZMod.finEquiv 3).injective
      rw [(ZMod.finEquiv 3).apply_symm_apply,← label t l,hl]
    subst k
    subst l
    apply transversal_pair_unique i j ij
    · rw [← indexed t i, ← indexed c i, hk, point_a]
    · rw [← indexed t j, ← indexed c j, hl, point_b]


/-- Transversals on the actual residue classes attain the internal bound. -/
theorem exists_internal_additions_attaining {d r : ℕ} [NeZero (3*r)] {T : Type*}
    (hd : 0 < d) (mixed : T → Fin 3 → Row d × ZMod (3*r))
    (family : LiftedLineFamily mixed)
    (distinct_rows : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (pair_unique : ∀ t u x y, x ≠ y →
      covers (mixed t) x y → covers (mixed u) x y → t = u) :
    let U := Row d × (ZMod r × ZMod r)
    ∃ internal : U → Fin 3 → Row d × ZMod (3*r),
      (∀ u i, (internal u i).1 = u.1) ∧
      (∀ t, Function.Injective (Sum.elim mixed internal t)) ∧
      (∀ t u x y, x ≠ y → covers (Sum.elim mixed internal t) x y →
        covers (Sum.elim mixed internal u) x y → t = u) ∧
      LiftedLineFamily (Sum.elim mixed internal) ∧ AllowsExtra (Sum.elim mixed internal) ∧
      Module.finrank (ZMod 3) (potentialSpace (Sum.elim mixed internal) 0) = d+1 ∧
      Nat.card U = 3^d * r^2 := by
  classical
  intro U
  let red := ZMod.castHom (dvd_mul_right 3 r) (ZMod 3)
  obtain ⟨row,hrow,hsums,hcover⟩ := residue_transversal r
  let internal (u : U) (i : Fin 3) := (u.1,row u.2 i)
  let combined := Sum.elim mixed internal
  have crosses (t : T) (x y : Row d × ZMod (3*r)) (hne : x ≠ y)
      (h : covers (mixed t) x y) : x.1 ≠ y.1 := by
    obtain ⟨i,j,hi,hj⟩ := h
    have ij : i ≠ j := fun eq => hne (hi.symm.trans (eq ▸ hj))
    rw [← hi,← hj]
    exact (distinct_rows t).ne ij
  have within (t : U) (x y : Row d × ZMod (3*r))
      (h : covers (internal t) x y) : x.1 = t.1 ∧ y.1 = t.1 := by
    obtain ⟨i,j,hi,hj⟩ := h
    exact ⟨congrArg Prod.fst hi.symm,congrArg Prod.fst hj.symm⟩
  have indexed (t : U) (x y : Row d × ZMod (3*r))
      (h : covers (internal t) x y) : covers (row t.2) x.2 y.2 := by
    obtain ⟨i,j,hi,hj⟩ := h
    exact ⟨i,j,congrArg Prod.snd hi,congrArg Prod.snd hj⟩
  have injective : ∀ t, Function.Injective (combined t) := by
    intro t i j h
    cases t with
    | inl t => exact distinct_rows t (congrArg Prod.fst h)
    | inr t => exact hrow t.2 (congrArg (fun x => red x.2) h)
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
          exact (hrow t.2).ne ij
        obtain ⟨a,_,ua⟩ := hcover x.2 y.2 dx
        apply congrArg Sum.inr
        exact Prod.ext ((within t x y ht).1.symm.trans (within u x y hu).1)
          ((ua t.2 (indexed t x y ht)).trans (ua u.2 (indexed u x y hu)).symm)
  have hfamily : LiftedLineFamily combined := by
    constructor
    · intro x y a b h
      obtain ⟨t,i,j,k,hij,hki,hkj,hi,hj,hk⟩ := family.1 x y a b h
      exact ⟨Sum.inl t,i,j,k,hij,hki,hkj,hi,hj,hk⟩
    · intro t
      cases t with
      | inl t => exact family.2 t
      | inr t => exact Or.inl (fun _ => rfl)
  have red_eq : cyclicReduction (3*r) = red.toAddMonoidHom := by
    unfold cyclicReduction
    rw [dite_eq_left (dvd_mul_right 3 r)]
  have extra : AllowsExtra combined := by
    refine ⟨dvd_mul_right 3 r,?_⟩
    rw [red_eq]
    constructor
    · intro x a b missing
      have e : red a = red b := by
        by_contra h
        obtain ⟨c,⟨i,j,hi,hj⟩,_⟩ := hcover a b h
        exact missing ⟨Sum.inr (x,c),i,j,Prod.ext rfl hi,Prod.ext rfl hj⟩
      change red (a-b) = 0
      rw [map_sub,e,sub_self]
    · intro t same
      cases t with
      | inl t =>
        have h : (mixed t 1).1 = (mixed t 0).1 := same 1
        exact False.elim ((by decide : (1 : Fin 3) ≠ 0) (distinct_rows t h))
      | inr t =>
        change red (∑ j, row t.2 j) = 0
        rw [map_sum]
        exact hsums t.2
  have dim := potential_finrank_internal_triples combined hd hfamily
  rw [ite_eq_left extra] at dim
  refine ⟨internal,fun _ _ => rfl,injective,pairUnique,hfamily,extra,dim,?_⟩
  have : NeZero r := ⟨by
    intro hr
    exact NeZero.ne (3*r) (by simp [hr])⟩
  change Nat.card (Row d × (ZMod r × ZMod r)) = _
  rw [Nat.card_prod,Nat.card_prod,Nat.card_zmod,Nat.card_eq_fintype_card (α := Row d)]
  simp [Row,ZMod.card,pow_two]

end D5.S3.Combinatorics.Matroids.RankThreeMinimumInternalAdditions
