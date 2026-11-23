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

end D5.S3.Combinatorics.Matroids.RankThreeInternalSteinerDecomposition
