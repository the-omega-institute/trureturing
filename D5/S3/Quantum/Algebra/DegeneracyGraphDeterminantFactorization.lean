/- GID: D5/S3/Quantum/Algebra/DegeneracyGraphDeterminantFactorization
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/DegeneracyGraphDeterminantFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact all-depth source determinant factorization with literal tail multiplicities. -/

import D5.S3.Quantum.Algebra.DegeneracyGraphDeterminantMultiplicity

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.Quantum.Algebra.DegeneracyGraphDeterminant

/-- An actually occurring ordered pair of distinct siblings at one source level. -/
abbrev SourceSiblingPair {L : ℕ} (T : SourceTree L) (i : Fin L) :=
  {pq : T.V i.succ × T.V i.succ //
    pq.1 < pq.2 ∧ T.parent i pq.1 = T.parent i pq.2}

noncomputable instance sourcePairTailWitnessFintype {L : ℕ} (T : SourceTree L)
    (i : Fin L) (p q : T.V i.succ) :
    Fintype (SourcePairTailWitness T i p q) := by
  classical
  letI : Fintype (StrictTailLevel i) := Fintype.ofFinite _
  letI : Fintype (SourcePairTailVector T i p q) := inferInstance
  change Fintype {d : SourcePairTailVector T i p q //
    (pairRootSurvivalSet T i p q (sourcePairTailThreshold T i p q d)).card = 2}
  exact inferInstance

noncomputable instance pairRetainingDegreeFintype {n : ℕ} (T : SourceTree (n + 2))
    (i : Fin (n + 1)) (p q : T.V i.castSucc.succ) :
    Fintype (PairRetainingDegree T i p q) := by
  classical
  unfold PairRetainingDegree
  exact inferInstance

/-- The literal source multiplicity from equation (6.27). -/
noncomputable def sourceExponent {L : ℕ} (T : SourceTree L) (i : Fin L)
    (pq : SourceSiblingPair T i) : ℕ :=
  Fintype.card (SourcePairTailWitness T i pq.1.1 pq.1.2)

/-- The all-level product in the source determinant factorization (6.22). -/
noncomputable def sourceFactorProduct {L : ℕ} (T : SourceTree L) : ℂ :=
  ∏ i : Fin L, ∏ pq : SourceSiblingPair T i,
    (T.label i pq.1.1 - T.label i pq.1.2) ^ sourceExponent T i pq

/-- Ordered sibling pairs in every occupied pruning branch are exactly original
ordered sibling pairs equipped with a degree which retains both endpoints. -/
private noncomputable def prunedSiblingPairEquiv {n : ℕ} (T : SourceTree (n + 2))
    (i : Fin (n + 1)) :
    (Σ r : OccupiedDegree T, SourceSiblingPair (prune T r.1.val r.2) i) ≃
      (Σ pq : SourceSiblingPair T i.castSucc,
        PairRetainingDegree T i pq.1.1 pq.1.2) where
  toFun x := by
    rcases x with ⟨r, pq⟩
    let p := pq.1.1.1
    let q := pq.1.2.1
    have hp : ∃ a : occupiedPenultimate T r.1.val,
        T.ancestor (show i.castSucc.succ ≤ (Fin.last (n + 1)).castSucc by
          change i.val + 1 ≤ n + 1; omega) a.1 = p := pq.1.1.2
    have hq : ∃ a : occupiedPenultimate T r.1.val,
        T.ancestor (show i.castSucc.succ ≤ (Fin.last (n + 1)).castSucc by
          change i.val + 1 ≤ n + 1; omega) a.1 = q := pq.1.2.2
    refine ⟨⟨(p, q), ?_, ?_⟩, ⟨r, hp, hq⟩⟩
    · exact pq.2.1
    · exact congrArg Subtype.val pq.2.2
  invFun x := by
    rcases x with ⟨pq, r⟩
    refine ⟨r.1, ⟨(⟨pq.1.1, r.2.1⟩, ⟨pq.1.2, r.2.2⟩), ?_, ?_⟩⟩
    · exact pq.2.1
    · apply Subtype.ext
      exact pq.2.2
  left_inv := by
    rintro ⟨r, pq⟩
    rfl
  right_inv := by
    rintro ⟨pq, r⟩
    rfl

/-- The nested fiber order used by the recurrence is the actual ordered bottom
sibling-pair index, with the source's earlier-minus-later orientation. -/
private noncomputable def bottomSiblingPairEquiv {n : ℕ} (T : SourceTree (n + 1)) :
    (Σ p : Penultimate T,
      Σ i : Fin (Fintype.card (bottomFiber T p)),
        {j : Fin (Fintype.card (bottomFiber T p)) // j ∈ Finset.Ioi i}) ≃
      SourceSiblingPair T (Fin.last n) := by
  classical
  let f : (Σ p : Penultimate T,
      Σ i : Fin (Fintype.card (bottomFiber T p)),
        {j : Fin (Fintype.card (bottomFiber T p)) // j ∈ Finset.Ioi i}) →
      SourceSiblingPair T (Fin.last n) := fun x => by
    rcases x with ⟨p, i, j⟩
    refine ⟨((fiberOrder T p i).1, (fiberOrder T p j.1).1), ?_, ?_⟩
    · exact (fiberOrder T p).lt_iff_lt.mpr (Finset.mem_Ioi.mp j.2)
    · exact (fiberOrder T p i).2.trans (fiberOrder T p j.1).2.symm
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨p, i, j⟩ ⟨q, k, l⟩ h
    have hpair := congrArg Subtype.val h
    have hfirst := congrArg Prod.fst hpair
    have hsecond := congrArg Prod.snd hpair
    have hpq : p = q := (fiberOrder T p i).2.symm.trans
      ((congrArg (bottomParent T) hfirst).trans (fiberOrder T q k).2)
    subst q
    have hik : i = k := (fiberOrder T p).injective (Subtype.ext hfirst)
    subst k
    have hjl : j = l := Subtype.ext ((fiberOrder T p).injective (Subtype.ext hsecond))
    subst l
    rfl
  · intro pq
    let p := bottomParent T pq.1.1
    let a : bottomFiber T p := bottomInFiber T pq.1.1
    let b : bottomFiber T p := ⟨pq.1.2, pq.2.2.symm⟩
    let i := (fiberOrder T p).symm a
    let j := (fiberOrder T p).symm b
    have hij : j ∈ Finset.Ioi i := by
      rw [Finset.mem_Ioi]
      apply (fiberOrder T p).lt_iff_lt.mp
      change ((fiberOrder T p) ((fiberOrder T p).symm a)).1 <
        ((fiberOrder T p) ((fiberOrder T p).symm b)).1
      rw [(fiberOrder T p).apply_symm_apply, (fiberOrder T p).apply_symm_apply]
      exact pq.2.1
    refine ⟨⟨p, i, ⟨j, hij⟩⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change ((fiberOrder T p) i).1 = pq.1.1
      rw [show i = (fiberOrder T p).symm a from rfl,
        (fiberOrder T p).apply_symm_apply]
      rfl
    · change ((fiberOrder T p) j).1 = pq.1.2
      rw [show j = (fiberOrder T p).symm b from rfl,
        (fiberOrder T p).apply_symm_apply]

private noncomputable def depthOneSiblingPairEquiv (T : SourceTree 1) :
    (Σ i : Fin (Fintype.card (Bottom T)),
      {j : Fin (Fintype.card (Bottom T)) // j ∈ Finset.Ioi i}) ≃
      SourceSiblingPair T 0 := by
  classical
  let order := depthOneBottomOrder T
  let f : (Σ i : Fin (Fintype.card (Bottom T)),
      {j : Fin (Fintype.card (Bottom T)) // j ∈ Finset.Ioi i}) →
      SourceSiblingPair T 0 := fun x =>
    ⟨(order x.1, order x.2.1),
      order.lt_iff_lt.mpr (Finset.mem_Ioi.mp x.2.2), T.rootSubsingleton.elim _ _⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨i, j⟩ ⟨k, l⟩ h
    have hpair := congrArg Subtype.val h
    have hik : i = k := order.injective (congrArg Prod.fst hpair)
    subst k
    have hjl : j = l := Subtype.ext (order.injective (congrArg Prod.snd hpair))
    subst l
    rfl
  · intro pq
    let i := order.symm pq.1.1
    let j := order.symm pq.1.2
    have hij : j ∈ Finset.Ioi i := by
      rw [Finset.mem_Ioi]
      apply order.lt_iff_lt.mp
      rw [order.apply_symm_apply, order.apply_symm_apply]
      exact pq.2.1
    refine ⟨⟨i, j, hij⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact order.apply_symm_apply pq.1.1
    · exact order.apply_symm_apply pq.1.2

set_option linter.style.haveILetI false in
/-- Exact arbitrary-depth source determinant factorization. The exponents are
the literal cardinalities in (6.27); the last level has exponent one, every
actual sibling exponent is positive, and the sole scalar is an integer unit. -/
theorem sourceSquare_det_factorization {n : ℕ} (T : SourceTree (n + 1)) :
    ∃ eps : ℤ,
      (eps = 1 ∨ eps = -1) ∧
      (SourceSquare T).det = (eps : ℂ) * sourceFactorProduct T ∧
      (∀ pq : SourceSiblingPair T (Fin.last n),
        sourceExponent T (Fin.last n) pq = 1) ∧
      (∀ (i : Fin (n + 1)) (pq : SourceSiblingPair T i),
        0 < sourceExponent T i pq) := by
  classical
  have exponentPositive {L : ℕ} (U : SourceTree L) (i : Fin L)
      (pq : SourceSiblingPair U i) : 0 < sourceExponent U i pq := by
    rw [sourceExponent, Fintype.card_pos_iff]
    let m : Exponents U := fun j => ⟨0, by
      rw [Fintype.card_pos_iff]
      let root : U.V 0 := Classical.choice inferInstance
      obtain ⟨v, _⟩ := U.ancestor_surjective (Fin.zero_le j.succ) root
      exact ⟨v⟩⟩
    have hall : ∀ (j : Fin (L + 1)) (v : U.V j),
        Survives U (sourceThreshold U m) j v := by
      intro j
      induction j using Fin.reverseInduction with
      | last =>
          intro v
          exact Survives.bottom v
      | cast j ih =>
          intro v
          obtain ⟨w, hw⟩ := U.ancestor_surjective Fin.castSucc_lt_succ.le v
          refine Survives.step j v {w} ?_ ?_ ?_
          · intro x hx
            have hxw : x = w := by simpa using hx
            subst x
            exact hw
          · simp [sourceThreshold, m]
          · intro x hx
            have hxw : x = w := by simpa using hx
            subst x
            exact ih w
    let a : AmbientPairTailWitness U i pq.1.1 pq.1.2 :=
      ⟨m, by
        refine ⟨?_, hall i.succ pq.1.1, hall i.succ pq.1.2⟩
        intro j hji
        rfl⟩
    exact ⟨(sourcePairTailWitnessEquivAmbient U i pq.1.1 pq.1.2
      (ne_of_lt pq.2.1)).symm a⟩
  have exponentBottom {m : ℕ} (U : SourceTree (m + 1))
      (pq : SourceSiblingPair U (Fin.last m)) :
      sourceExponent U (Fin.last m) pq = 1 := by
    rw [sourceExponent, Fintype.card_eq_one_iff]
    have hpos := exponentPositive U (Fin.last m) pq
    rw [sourceExponent, Fintype.card_pos_iff] at hpos
    obtain ⟨w⟩ := hpos
    refine ⟨w, ?_⟩
    intro y
    apply Subtype.ext
    funext j
    have hj := j.2
    change m + 1 ≤ j.1.val at hj
    have hjlt := j.1.isLt
    omega
  have hpositive := exponentPositive T
  have hbottomOne := exponentBottom T
  have hfactorization : ∃ eps : ℤ, (eps = 1 ∨ eps = -1) ∧
      (SourceSquare T).det = (eps : ℂ) * sourceFactorProduct T := by
    clear hpositive hbottomOne
    induction n with
    | zero =>
        let order := depthOneBottomOrder T
        let values : Fin (Fintype.card (Bottom T)) → ℂ :=
          fun i => T.label 0 (order i)
        have hmatrix :
            Matrix.reindex order.symm.toEquiv order.symm.toEquiv (SourceSquare T) =
              Matrix.vandermonde values := by
          ext i j
          simp only [OrderIso.toEquiv_symm, Matrix.reindex_apply, Equiv.symm_symm,
            RelIso.coe_fn_toEquiv, Matrix.submatrix_apply, Matrix.vandermonde_apply]
          change RawM T (order i) (bottomColumnEquiv T (order j)) = values i ^ j.val
          rw [show bottomColumnEquiv T (order j) =
            (depthOneColumnsEquiv T).symm j by simp [bottomColumnEquiv, order]]
          simp only [RawM, values]
          rw [Fin.prod_univ_one]
          rw [T.ancestor_self]
          change T.label 0 (order i) ^ j.val = T.label 0 (order i) ^ j.val
          rfl
        have hdet : (SourceSquare T).det = (Matrix.vandermonde values).det := by
          rw [← Matrix.det_reindex_self order.symm.toEquiv (SourceSquare T), hmatrix]
        let eps : ℤ := ∏ i : Fin (Fintype.card (Bottom T)),
          ∏ _j ∈ Finset.Ioi i, (-1 : ℤ)
        have heps : eps = 1 ∨ eps = -1 := by
          apply Int.isUnit_iff.mp
          dsimp only [eps]
          apply (IsUnit.prod_univ_iff).mpr
          intro i
          apply (IsUnit.prod_iff).mpr
          intro j hj
          exact isUnit_neg_one
        have horientation : (Matrix.vandermonde values).det =
            (eps : ℂ) * ∏ i : Fin (Fintype.card (Bottom T)),
              ∏ j ∈ Finset.Ioi i, (values i - values j) := by
          rw [Matrix.det_vandermonde]
          have hcast : (eps : ℂ) = ∏ i : Fin (Fintype.card (Bottom T)),
              ∏ _j ∈ Finset.Ioi i, (-1 : ℂ) := by
            simp [eps]
          rw [hcast]
          simp_rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro i hi
          apply Finset.prod_congr rfl
          intro j hj
          ring
        have hordered : (∏ i : Fin (Fintype.card (Bottom T)),
            ∏ j ∈ Finset.Ioi i, (values i - values j)) =
            ∏ pq : SourceSiblingPair T 0,
              (T.label 0 pq.1.1 - T.label 0 pq.1.2) := by
          have hattach (i : Fin (Fintype.card (Bottom T))) :
              (Finset.Ioi i).prod (fun j => values i - values j) =
                (Finset.univ : Finset {j : Fin (Fintype.card (Bottom T)) //
                  j ∈ Finset.Ioi i}).prod (fun j => values i - values j.1) := by
            exact (Finset.prod_coe_sort (s := Finset.Ioi i)
              (f := fun j => values i - values j)).symm
          simp_rw [hattach]
          rw [← Fintype.prod_sigma']
          apply Fintype.prod_equiv (depthOneSiblingPairEquiv T)
          intro x
          rcases x with ⟨i, j⟩
          rfl
        have hfactor : sourceFactorProduct T =
            ∏ pq : SourceSiblingPair T 0,
              (T.label 0 pq.1.1 - T.label 0 pq.1.2) := by
          unfold sourceFactorProduct
          rw [Fin.prod_univ_one]
          apply Fintype.prod_congr
          intro pq
          have he := exponentBottom T pq
          change sourceExponent T 0 pq = 1 at he
          rw [he, pow_one]
        refine ⟨eps, heps, ?_⟩
        rw [hdet, horientation, hordered, ← hfactor]
    | succ n ih =>
        let epsr (r : OccupiedDegree T) : ℤ :=
          Classical.choose (ih (prune T r.1.val r.2))
        have hepsr (r : OccupiedDegree T) : epsr r = 1 ∨ epsr r = -1 :=
          (Classical.choose_spec (ih (prune T r.1.val r.2))).1
        have hdetr (r : OccupiedDegree T) :
            (SourceSquare (prune T r.1.val r.2)).det =
              (epsr r : ℂ) * sourceFactorProduct (prune T r.1.val r.2) :=
          (Classical.choose_spec (ih (prune T r.1.val r.2))).2
        have hrecurrenceSign :
            pruningRecurrenceSign T = 1 ∨ pruningRecurrenceSign T = -1 := by
          apply Int.isUnit_iff.mp
          unfold pruningRecurrenceSign
          apply IsUnit.mul
          · exact (Equiv.Perm.sign (pruningPermutation T)).isUnit
          · apply (IsUnit.prod_iff).mpr
            intro p hp
            unfold fiberOrientationSign
            apply (IsUnit.prod_univ_iff).mpr
            intro i
            apply (IsUnit.prod_iff).mpr
            intro j hj
            exact isUnit_neg_one
        have hbottomFactor :
            (∏ p ∈ Finset.univ.image (bottomParent T),
              sourceSiblingVandermonde T p) =
              ∏ pq : SourceSiblingPair T (Fin.last (n + 1)),
                (T.label (Fin.last (n + 1)) pq.1.1 -
                  T.label (Fin.last (n + 1)) pq.1.2) := by
          have hsurj : Function.Surjective (bottomParent T) := by
            intro p
            obtain ⟨b, hb⟩ := T.ancestor_surjective Fin.castSucc_lt_succ.le p
            exact ⟨b, hb⟩
          have himage : Finset.univ.image (bottomParent T) = Finset.univ := by
            apply Finset.eq_univ_of_forall
            intro p
            obtain ⟨b, rfl⟩ := hsurj p
            exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
          rw [himage]
          simp only [sourceSiblingVandermonde]
          have hattach (p : Penultimate T)
              (i : Fin (Fintype.card (bottomFiber T p))) :
              (Finset.Ioi i).prod (fun j => fiberValues T p i - fiberValues T p j) =
                (Finset.univ : Finset {j : Fin (Fintype.card (bottomFiber T p)) //
                  j ∈ Finset.Ioi i}).prod
                    (fun j => fiberValues T p i - fiberValues T p j.1) := by
            exact (Finset.prod_coe_sort (s := Finset.Ioi i)
              (f := fun j => fiberValues T p i - fiberValues T p j)).symm
          simp_rw [hattach]
          rw [← Fintype.prod_sigma', ← Fintype.prod_sigma']
          let e := (Equiv.sigmaAssoc (fun (p : Penultimate T)
            (i : Fin (Fintype.card (bottomFiber T p))) =>
              {j : Fin (Fintype.card (bottomFiber T p)) // j ∈ Finset.Ioi i})).trans
                (bottomSiblingPairEquiv T)
          apply Fintype.prod_equiv e
          intro x
          rcases x with ⟨p, i, j⟩
          rfl
        have hupperFactor :
            (∏ r : OccupiedDegree T, sourceFactorProduct (prune T r.1.val r.2)) =
              ∏ i : Fin (n + 1), ∏ pq : SourceSiblingPair T i.castSucc,
                (T.label i.castSucc pq.1.1 - T.label i.castSucc pq.1.2) ^
                  sourceExponent T i.castSucc pq := by
          simp only [sourceFactorProduct]
          rw [Finset.prod_comm]
          apply Fintype.prod_congr
          intro i
          rw [← Fintype.prod_sigma']
          let e := prunedSiblingPairEquiv T i
          let retainedPair (pq : SourceSiblingPair T i.castSucc)
              (r : PairRetainingDegree T i pq.1.1 pq.1.2) :
              SourceSiblingPair (prune T r.1.1.val r.1.2) i :=
            ⟨(⟨pq.1.1, r.2.1⟩, ⟨pq.1.2, r.2.2⟩), pq.2.1, by
              apply Subtype.ext
              exact pq.2.2⟩
          let g : (Σ pq : SourceSiblingPair T i.castSucc,
              PairRetainingDegree T i pq.1.1 pq.1.2) → ℂ := fun x =>
            (T.label i.castSucc x.1.1.1 - T.label i.castSucc x.1.1.2) ^
              sourceExponent (prune T x.2.1.1.val x.2.1.2) i (retainedPair x.1 x.2)
          calc
            _ = ∏ x, g x := Fintype.prod_equiv e _ g (by
              rintro ⟨r, pq⟩
              rfl)
            _ = ∏ pq : SourceSiblingPair T i.castSucc,
                (T.label i.castSucc pq.1.1 - T.label i.castSucc pq.1.2) ^
                  sourceExponent T i.castSucc pq := by
              rw [Fintype.prod_sigma]
              apply Fintype.prod_congr
              intro pq
              letI : ∀ r : PairRetainingDegree T i pq.1.1 pq.1.2,
                  Fintype (SourcePairTailWitness (prune T r.1.1.val r.1.2) i
                    (⟨pq.1.1, r.2.1⟩ : (prune T r.1.1.val r.1.2).V i.succ)
                    (⟨pq.1.2, r.2.2⟩ : (prune T r.1.1.val r.1.2).V i.succ)) :=
                fun r => sourcePairTailWitnessFintype _ _ _ _
              have hcard : sourceExponent T i.castSucc pq =
                  ∑ r : PairRetainingDegree T i pq.1.1 pq.1.2,
                    sourceExponent (prune T r.1.1.val r.1.2) i
                      (retainedPair pq r) := by
                unfold sourceExponent
                rw [show Fintype.card
                    (SourcePairTailWitness T i.castSucc pq.1.1 pq.1.2) =
                    Fintype.card (Σ r : PairRetainingDegree T i pq.1.1 pq.1.2,
                      SourcePairTailWitness (prune T r.1.1.val r.1.2) i
                        (⟨pq.1.1, r.2.1⟩ : (prune T r.1.1.val r.1.2).V i.succ)
                        (⟨pq.1.2, r.2.2⟩ : (prune T r.1.1.val r.1.2).V i.succ)) from
                  Fintype.card_congr (sourcePairTailPruningEquiv T i pq.1.1 pq.1.2
                    pq.2.1 pq.2.2)]
                exact Fintype.card_sigma
              change (∏ r : PairRetainingDegree T i pq.1.1 pq.1.2,
                  (T.label i.castSucc pq.1.1 - T.label i.castSucc pq.1.2) ^
                    sourceExponent (prune T r.1.1.val r.1.2) i
                      (retainedPair pq r)) = _
              rw [hcard]
              exact Finset.prod_pow_eq_pow_sum Finset.univ _ _
        let eps : ℤ := pruningRecurrenceSign T * ∏ r : OccupiedDegree T, epsr r
        have heps : eps = 1 ∨ eps = -1 := by
          apply Int.isUnit_iff.mp
          dsimp only [eps]
          apply IsUnit.mul
          · exact Int.isUnit_iff.mpr hrecurrenceSign
          · apply (IsUnit.prod_univ_iff).mpr
            intro r
            exact Int.isUnit_iff.mpr (hepsr r)
        have hbottomexp :
            (∏ pq : SourceSiblingPair T (Fin.last (n + 1)),
              (T.label (Fin.last (n + 1)) pq.1.1 -
                T.label (Fin.last (n + 1)) pq.1.2) ^
                  sourceExponent T (Fin.last (n + 1)) pq) =
              ∏ p ∈ Finset.univ.image (bottomParent T),
                sourceSiblingVandermonde T p := by
          rw [hbottomFactor]
          apply Fintype.prod_congr
          intro pq
          rw [exponentBottom T pq, pow_one]
        have hwhole : sourceFactorProduct T =
            (∏ i : Fin (n + 1), ∏ pq : SourceSiblingPair T i.castSucc,
              (T.label i.castSucc pq.1.1 - T.label i.castSucc pq.1.2) ^
                sourceExponent T i.castSucc pq) *
            (∏ p ∈ Finset.univ.image (bottomParent T),
              sourceSiblingVandermonde T p) := by
          unfold sourceFactorProduct
          rw [Fin.prod_univ_castSucc, hbottomexp]
        refine ⟨eps, heps, ?_⟩
        rw [sourceSquare_det_pruning_recurrence]
        simp_rw [hdetr]
        rw [Finset.prod_mul_distrib, hupperFactor, hwhole]
        simp only [eps, Int.cast_mul, Int.cast_prod]
        ring
  obtain ⟨eps, heps, hdet⟩ := hfactorization
  exact ⟨eps, heps, hdet, hbottomOne, hpositive⟩

#print axioms sourceSquare_det_factorization

end D5.S3.Quantum.Algebra.DegeneracyGraphDeterminant
