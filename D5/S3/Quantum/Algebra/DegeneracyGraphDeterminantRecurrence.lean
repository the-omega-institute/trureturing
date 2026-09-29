/- GID: D5/S3/Quantum/Algebra/DegeneracyGraphDeterminantRecurrence
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/DegeneracyGraphDeterminantRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Global square reindexing and the occupied fiber-Newton determinant recurrence. -/

import D5.S3.Quantum.Algebra.DegeneracyGraphDeterminant

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.Quantum.Algebra.DegeneracyGraphDeterminant

/-- Newton degrees which occur in at least one actual bottom fiber. -/
abbrev OccupiedDegree {n : ℕ} (T : SourceTree (n + 1)) :=
  {r : Fin (Fintype.card (Bottom T)) // Nonempty (occupiedPenultimate T r.val)}

noncomputable instance occupiedDegreeFintype {n : ℕ} (T : SourceTree (n + 1)) :
    Fintype (OccupiedDegree T) :=
  Fintype.ofFinite _

abbrev DegreeParent {n : ℕ} (T : SourceTree (n + 1)) :=
  {x : Fin (Fintype.card (Bottom T)) × Penultimate T //
    x.1.val < Fintype.card (bottomFiber T x.2)}

/-- Bottom vertices grouped by their Newton rank and then by the occupied parent fiber. -/
noncomputable def bottomDegreeEquiv {n : ℕ} (T : SourceTree (n + 1)) :
    Bottom T ≃ DegreeParent T where
  toFun b := by
    have hrank := fiberRank_order T (bottomParent T b)
      ((fiberOrder T (bottomParent T b)).symm (bottomInFiber T b))
    rw [(fiberOrder T (bottomParent T b)).apply_symm_apply] at hrank
    change fiberRank T b = _ at hrank
    have hfiber : fiberRank T b <
        Fintype.card (bottomFiber T (bottomParent T b)) := by
      rw [hrank]
      exact ((fiberOrder T (bottomParent T b)).symm (bottomInFiber T b)).isLt
    let r : Fin (Fintype.card (Bottom T)) :=
      ⟨fiberRank T b, hfiber.trans_le (Fintype.card_subtype_le _)⟩
    exact ⟨(r, bottomParent T b), hfiber⟩
  invFun x :=
    (fiberOrder T x.1.2 ⟨x.1.1.val, x.2⟩).1
  left_inv := by
    intro b
    have hrank := fiberRank_order T (bottomParent T b)
      ((fiberOrder T (bottomParent T b)).symm (bottomInFiber T b))
    rw [(fiberOrder T (bottomParent T b)).apply_symm_apply] at hrank
    change fiberRank T b = _ at hrank
    change (fiberOrder T (bottomParent T b) ⟨fiberRank T b, _⟩).1 = b
    have hi : (⟨fiberRank T b, by rw [hrank]; exact
        ((fiberOrder T (bottomParent T b)).symm (bottomInFiber T b)).isLt⟩ :
        Fin (Fintype.card (bottomFiber T (bottomParent T b)))) =
        (fiberOrder T (bottomParent T b)).symm (bottomInFiber T b) :=
      Fin.ext hrank
    rw [hi, (fiberOrder T (bottomParent T b)).apply_symm_apply]
    rfl
  right_inv := by
    rintro ⟨⟨⟨r, hr⟩, p⟩, hp⟩
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      exact fiberRank_order T p ⟨r, hp⟩
    · exact (fiberOrder T p ⟨r, hp⟩).2

noncomputable def columnDegree {n : ℕ} (T : SourceTree (n + 2))
    (m : Columns T) : OccupiedDegree T :=
  ⟨m.1 (Fin.last (n + 1)), column_last_occupied T m⟩

noncomputable def columnDegreeFiberEquiv {n : ℕ} (T : SourceTree (n + 2))
    (r : OccupiedDegree T) :
    {m : Columns T // columnDegree T m = r} ≃
      Columns (prune T r.1.val r.2) where
  toFun m := lastExponentSliceEquiv T r.1.val r.2
    ⟨m.1, congrArg (fun q : OccupiedDegree T => q.1.val) m.2⟩
  invFun m := ⟨liftColumn T r.1.val r.2 m, by
    apply Subtype.ext
    apply Fin.ext
    simp [columnDegree, liftColumn, liftExponents]⟩
  left_inv := by
    intro m
    apply Subtype.ext
    apply Subtype.ext
    have hlast : (m.1.1 (Fin.last (n + 1))).val = r.1.val := by
      simpa only [columnDegree] using
        congrArg (fun q : OccupiedDegree T => q.1.val) m.2
    change liftExponents T r.1.val r.2
      (restrictExponents T m.1 r.1.val
        hlast r.2) = m.1.1
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · apply Fin.ext
      simpa [liftExponents] using hlast.symm
    · apply Fin.ext
      simp [liftExponents, restrictExponents]
  right_inv := (lastExponentSliceEquiv T r.1.val r.2).right_inv

/-- Literal columns grouped by their occupied last exponent. -/
noncomputable def columnDegreeEquiv {n : ℕ} (T : SourceTree (n + 2)) :
    Columns T ≃ Σ r : OccupiedDegree T, Columns (prune T r.1.val r.2) :=
  (Equiv.sigmaFiberEquiv (columnDegree T)).symm.trans
    (Equiv.sigmaCongrRight (columnDegreeFiberEquiv T))

/-- The pair indexing of actual Newton rows as a dependent occupied-degree sum. -/
noncomputable def degreeParentEquiv {n : ℕ} (T : SourceTree (n + 1)) :
    DegreeParent T ≃ Σ r : OccupiedDegree T, occupiedPenultimate T r.1.val where
  toFun x := ⟨⟨x.1.1, ⟨x.1.2, x.2⟩⟩, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨(x.1.1, x.2.1), x.2.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    rintro ⟨r, p⟩
    apply Sigma.subtype_ext
    · exact Subtype.ext rfl
    · rfl

/-- The bottom level of `T_r` consists literally of the occupied penultimate
vertices of `T`; this equivalence only removes the inherited-subtype proofs. -/
noncomputable def pruneBottomEquiv {n : ℕ} (T : SourceTree (n + 2))
    (r : ℕ) (hoccupied : Nonempty (occupiedPenultimate T r)) :
    Bottom (prune T r hoccupied) ≃ occupiedPenultimate T r where
  toFun v := by
    let p : occupiedPenultimate T r := Classical.choose v.2
    have hp := Classical.choose_spec v.2
    refine ⟨v.1, ?_⟩
    change T.ancestor (le_refl _) p.1 = v.1 at hp
    have hpv : p.1 = v.1 := by simpa only [T.ancestor_self] using hp
    simpa only [hpv] using p.2
  invFun p := ⟨p.1, p, T.ancestor_self _ p.1⟩
  left_inv := by intro v; exact Subtype.ext rfl
  right_inv := by intro p; exact Subtype.ext rfl

/-- Explicit squareness of the source ancestor matrix, recursively induced by
the occupied pruning decomposition. -/
noncomputable def bottomColumnEquiv : {L : ℕ} → (T : SourceTree (L + 1)) →
    Bottom T ≃ Columns T
  | 0, T => (depthOneBottomOrder T).symm.toEquiv.trans (depthOneColumnsEquiv T).symm
  | _n + 1, T =>
      (bottomDegreeEquiv T).trans
        ((degreeParentEquiv T).trans
          ((Equiv.sigmaCongrRight fun r =>
            (pruneBottomEquiv T r.1.val r.2).symm.trans
              (bottomColumnEquiv (prune T r.1.val r.2))).trans
            (columnDegreeEquiv T).symm))

/-- Bottom vertices indexed by their actual parent and their increasing place
inside that parent's fiber. -/
noncomputable def bottomFiberOrderEquiv {n : ℕ} (T : SourceTree (n + 1)) :
    Bottom T ≃ Σ p : Penultimate T, Fin (Fintype.card (bottomFiber T p)) where
  toFun b := by
    have hrank := fiberRank_order T (bottomParent T b)
      ((fiberOrder T (bottomParent T b)).symm (bottomInFiber T b))
    rw [(fiberOrder T (bottomParent T b)).apply_symm_apply] at hrank
    change fiberRank T b = _ at hrank
    exact ⟨bottomParent T b, ⟨fiberRank T b, hrank ▸
      ((fiberOrder T (bottomParent T b)).symm (bottomInFiber T b)).isLt⟩⟩
  invFun x := (fiberOrder T x.1 x.2).1
  left_inv := by
    intro b
    have hrank := fiberRank_order T (bottomParent T b)
      ((fiberOrder T (bottomParent T b)).symm (bottomInFiber T b))
    rw [(fiberOrder T (bottomParent T b)).apply_symm_apply] at hrank
    change fiberRank T b = _ at hrank
    have hi : (⟨fiberRank T b, by rw [hrank]; exact
        ((fiberOrder T (bottomParent T b)).symm (bottomInFiber T b)).isLt⟩ :
        Fin (Fintype.card (bottomFiber T (bottomParent T b)))) =
        (fiberOrder T (bottomParent T b)).symm (bottomInFiber T b) := Fin.ext hrank
    change (fiberOrder T (bottomParent T b)
      ⟨fiberRank T b, _⟩).1 = b
    rw [hi, (fiberOrder T (bottomParent T b)).apply_symm_apply]
    rfl
  right_inv := by
    rintro ⟨p, i⟩
    dsimp only
    let hp := (fiberOrder T p i).2
    apply Sigma.ext hp
    apply (Fin.heq_ext_iff (congrArg
      (fun q => Fintype.card (bottomFiber T q)) hp)).mpr
    exact fiberRank_order T p i

theorem NewtonE_inv_reindex_fibers {n : ℕ} (T : SourceTree (n + 1)) :
    Matrix.reindex (bottomFiberOrderEquiv T) (bottomFiberOrderEquiv T) (NewtonE T)⁻¹ =
      Matrix.blockDiagonal' (fun p => (fiberEvaluation T p)⁻¹) := by
  classical
  have hNewtonE :
      Matrix.reindex (bottomFiberOrderEquiv T) (bottomFiberOrderEquiv T) (NewtonE T) =
        Matrix.blockDiagonal' (fiberEvaluation T) := by
    ext ⟨p, i⟩ ⟨q, j⟩
    by_cases hpq : p = q
    · subst q
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.blockDiagonal'_apply_eq]
      change NewtonE T (fiberOrder T p i).1 (fiberOrder T p j).1 =
        fiberEvaluation T p i j
      have hi : bottomParent T (fiberOrder T p i).1 = p := (fiberOrder T p i).2
      have hj : bottomParent T (fiberOrder T p j).1 = p := (fiberOrder T p j).2
      simp only [NewtonE, dif_pos (hi.trans hj.symm), fiberEvaluation, fiberValues]
      rw [hj, fiberRank_order]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.blockDiagonal'_apply_ne _ _ _ hpq]
      change (if _h : bottomParent T (fiberOrder T p i).1 =
          bottomParent T (fiberOrder T q j).1 then _ else 0) = 0
      have hne : bottomParent T (fiberOrder T p i).1 ≠
          bottomParent T (fiberOrder T q j).1 := fun h =>
        hpq ((fiberOrder T p i).2.symm.trans (h.trans (fiberOrder T q j).2))
      rw [dif_neg hne]
  have hdegree (p : Penultimate T)
      (e : Fin (Fintype.card (bottomFiber T p))) :
      (fiberNewton T p e.val).natDegree = e := by
    rw [fiberNewton, Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
    have hs : (Finset.univ.filter fun j : Fin (Fintype.card (bottomFiber T p)) =>
        j.val < e.val) = Finset.Iio e := by
      ext j
      simp
    rw [hs, Fin.card_Iio]
  have hmonic (p : Penultimate T) (e : ℕ) : (fiberNewton T p e).Monic := by
    apply Polynomial.monic_prod_of_monic
    intro j hj
    exact Polynomial.monic_X_sub_C _
  have hfiber (p : Penultimate T) : (fiberEvaluation T p).det ≠ 0 := by
    rw [show (fiberEvaluation T p).det =
        (Matrix.vandermonde (fiberValues T p)).det by
      symm
      exact Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
        (fiberValues T p) (fun i => fiberNewton T p i.val) (hdegree p)
          (fun i => hmonic p i.val)]
    apply Matrix.det_vandermonde_ne_zero_iff.mpr
    intro i j hij
    apply (fiberOrder T p).injective
    apply Subtype.ext
    apply T.sibling_injective (Fin.last n)
    · exact (fiberOrder T p i).2.trans (fiberOrder T p j).2.symm
    · exact hij
  have hinv : (Matrix.blockDiagonal' (fiberEvaluation T))⁻¹ =
      Matrix.blockDiagonal' (fun p => (fiberEvaluation T p)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.blockDiagonal'_mul]
    have h := congrArg Matrix.blockDiagonal'
      (funext fun p => Matrix.nonsing_inv_mul (fiberEvaluation T p)
        (isUnit_iff_ne_zero.mpr (hfiber p)))
    exact h.trans Matrix.blockDiagonal'_one
  rw [← Matrix.inv_reindex, hNewtonE, hinv]

noncomputable def ancestorPrefix {n : ℕ} (T : SourceTree (n + 2))
    (p : Penultimate T) (m : Columns T) : ℂ :=
  ∏ i : Fin (n + 1),
    T.label i.castSucc (T.ancestor
      (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i.succ)) p) ^
      (m.1 i.castSucc).val

abbrev PruningIndex {n : ℕ} (T : SourceTree (n + 2)) :=
  Σ r : OccupiedDegree T, occupiedPenultimate T r.1.val

noncomputable instance pruningIndexFintype {n : ℕ} (T : SourceTree (n + 2)) :
    Fintype (PruningIndex T) :=
  Fintype.ofFinite _

noncomputable def pruningRowEquiv {n : ℕ} (T : SourceTree (n + 2)) :
    Bottom T ≃ PruningIndex T :=
  (bottomDegreeEquiv T).trans (degreeParentEquiv T)

noncomputable def pruningColumnEquiv {n : ℕ} (T : SourceTree (n + 2)) :
    Columns T ≃ PruningIndex T :=
  (columnDegreeEquiv T).trans (Equiv.sigmaCongrRight fun r =>
    (bottomColumnEquiv (prune T r.1.val r.2)).symm.trans
      (pruneBottomEquiv T r.1.val r.2))

/-- The actual inverse-Newton transform, with rows and literal source columns
reindexed by occupied degree and retained parent. -/
noncomputable def NewtonPruningMatrix {n : ℕ} (T : SourceTree (n + 2)) :
    Matrix (PruningIndex T) (PruningIndex T) ℂ :=
  Matrix.reindex (pruningRowEquiv T) (pruningColumnEquiv T)
    ((NewtonE T)⁻¹ * RawM T)

def pruningDegree {n : ℕ} {T : SourceTree (n + 2)}
    (x : PruningIndex T) : OccupiedDegree T :=
  x.1

/-- A transformed entry below the actual fiber size is the ancestor prefix
times the genuine inverse-Newton coefficient.  No statement is made about
degrees outside that fiber's interpolation range. -/
theorem NewtonPruningMatrix_apply_low {n : ℕ} (T : SourceTree (n + 2))
    (r e : OccupiedDegree T)
    (p : occupiedPenultimate T r.1.val)
    (q : occupiedPenultimate T e.1.val)
    (he : e.1.val < Fintype.card (bottomFiber T p.1)) :
    NewtonPruningMatrix T ⟨r, p⟩ ⟨e, q⟩ =
      ancestorPrefix T p.1
          (liftColumn T e.1.val e.2
            (bottomColumnEquiv (prune T e.1.val e.2)
              ((pruneBottomEquiv T e.1.val e.2).symm q))) *
        (fiberCoefficient T p.1)⁻¹ ⟨r.1.val, p.2⟩
          ⟨e.1.val, he⟩ := by
  classical
  let m : Columns T :=
    liftColumn T e.1.val e.2
      (bottomColumnEquiv (prune T e.1.val e.2)
        ((pruneBottomEquiv T e.1.val e.2).symm q))
  let ri : Fin (Fintype.card (bottomFiber T p.1)) := ⟨r.1.val, p.2⟩
  have he' :
      (m.1 (Fin.last (n + 1))).val < Fintype.card (bottomFiber T p.1) := by
    dsimp only [m]
    simpa [liftColumn, liftExponents] using he
  have hfin :
      (⟨(m.1 (Fin.last (n + 1))).val, he'⟩ :
        Fin (Fintype.card (bottomFiber T p.1))) = ⟨e.1.val, he⟩ := by
    apply Fin.ext
    simp [m, liftColumn, liftExponents]
  change ((NewtonE T)⁻¹ * RawM T)
      ((pruningRowEquiv T).symm ⟨r, p⟩)
      ((pruningColumnEquiv T).symm ⟨e, q⟩) = _
  rw [show (pruningRowEquiv T).symm ⟨r, p⟩ =
      (fiberOrder T p.1 ⟨r.1.val, p.2⟩).1 from rfl]
  rw [show (pruningColumnEquiv T).symm ⟨e, q⟩ =
      liftColumn T e.1.val e.2
        (bottomColumnEquiv (prune T e.1.val e.2)
          ((pruneBottomEquiv T e.1.val e.2).symm q)) from rfl]
  change ((NewtonE T)⁻¹ * RawM T) (fiberOrder T p.1 ri).1 m =
    ancestorPrefix T p.1 m * (fiberCoefficient T p.1)⁻¹ ri ⟨e.1.val, he⟩
  rw [← hfin]
  have hsame (parent : Penultimate T)
      (i j : Fin (Fintype.card (bottomFiber T parent))) :
      (NewtonE T)⁻¹ (fiberOrder T parent i).1 (fiberOrder T parent j).1 =
        (fiberEvaluation T parent)⁻¹ i j := by
    have h := congrFun (congrFun (NewtonE_inv_reindex_fibers T)
      ⟨parent, i⟩) ⟨parent, j⟩
    change (NewtonE T)⁻¹ (fiberOrder T parent i).1
      (fiberOrder T parent j).1 = _ at h
    simpa only [Matrix.blockDiagonal'_apply_eq] using h
  have hoff (parent : Penultimate T)
      (i : Fin (Fintype.card (bottomFiber T p.1)))
      (j : Fin (Fintype.card (bottomFiber T parent))) (hpparent : p.1 ≠ parent) :
      (NewtonE T)⁻¹ (fiberOrder T p.1 i).1
        (fiberOrder T parent j).1 = 0 := by
    have h := congrFun (congrFun (NewtonE_inv_reindex_fibers T)
      ⟨p.1, i⟩) ⟨parent, j⟩
    change (NewtonE T)⁻¹ (fiberOrder T p.1 i).1
      (fiberOrder T parent j).1 = _ at h
    simpa only [Matrix.blockDiagonal'_apply_ne _ _ _ hpparent] using h
  have hRawM (parent : Penultimate T) (b : bottomFiber T parent) :
      RawM T b.1 m = ancestorPrefix T parent m *
        T.label (Fin.last (n + 1)) b.1 ^ (m.1 (Fin.last (n + 1))).val := by
    rw [RawM, Fin.prod_univ_castSucc]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      have hancestor :
          T.ancestor (Fin.le_last i.castSucc.succ) b.1 =
            T.ancestor (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i.succ))
              (bottomParent T b.1) := by
        exact (T.ancestor_trans
          (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i.succ))
          Fin.castSucc_lt_succ.le b.1).symm
      rw [hancestor]
      congr 2
      exact congrArg
        (T.ancestor (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i.succ))) b.2
    · rw [T.ancestor_self]
  have hdegree (parent : Penultimate T)
      (degree : Fin (Fintype.card (bottomFiber T parent))) :
      (fiberNewton T parent degree.val).natDegree = degree := by
    rw [fiberNewton, Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
    have hs : (Finset.univ.filter
        fun j : Fin (Fintype.card (bottomFiber T parent)) =>
          j.val < degree.val) = Finset.Iio degree := by
      ext j
      simp
    rw [hs, Fin.card_Iio]
  have hmonic (parent : Penultimate T) (degree : ℕ) :
      (fiberNewton T parent degree).Monic := by
    apply Polynomial.monic_prod_of_monic
    intro j hj
    exact Polynomial.monic_X_sub_C _
  have hcoefficient
      (i degree : Fin (Fintype.card (bottomFiber T p.1))) :
      ∑ j, (fiberEvaluation T p.1)⁻¹ i j *
          (fiberValues T p.1 j) ^ degree.val =
        (fiberCoefficient T p.1)⁻¹ i degree := by
    let E := fiberEvaluation T p.1
    let C := fiberCoefficient T p.1
    have hEdet : E.det = (Matrix.vandermonde (fiberValues T p.1)).det := by
      dsimp only [E]
      symm
      exact Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
        (fiberValues T p.1) (fun k => fiberNewton T p.1 k.val) (hdegree p.1)
          (fun k => hmonic p.1 k.val)
    have hinj : Function.Injective (fiberValues T p.1) := by
      intro a b hab
      apply (fiberOrder T p.1).injective
      apply Subtype.ext
      apply T.sibling_injective (Fin.last (n + 1))
      · exact (fiberOrder T p.1 a).2.trans (fiberOrder T p.1 b).2.symm
      · exact hab
    have hE : IsUnit E.det := by
      rw [hEdet]
      exact isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
    have hCdet : C.det = 1 := by
      dsimp only [C]
      exact Matrix.det_matrixOfPolynomials (fun k => fiberNewton T p.1 k.val)
        (hdegree p.1) (fun k => hmonic p.1 k.val)
    have hC : IsUnit C.det := by rw [hCdet]; exact isUnit_one
    have hfactor : E = Matrix.vandermonde (fiberValues T p.1) * C := by
      dsimp only [E, C]
      exact Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials
        (fiberValues T p.1) (fun k => fiberNewton T p.1 k.val)
          (fun k => Nat.le_of_eq (hdegree p.1 k))
    have hVC : Matrix.vandermonde (fiberValues T p.1) = E * C⁻¹ := by
      rw [hfactor, Matrix.mul_assoc, Matrix.mul_nonsing_inv C hC, Matrix.mul_one]
    have hinvmul : E⁻¹ * Matrix.vandermonde (fiberValues T p.1) = C⁻¹ := by
      calc
        E⁻¹ * Matrix.vandermonde (fiberValues T p.1) = E⁻¹ * (E * C⁻¹) := by rw [hVC]
        _ = (E⁻¹ * E) * C⁻¹ := by rw [Matrix.mul_assoc]
        _ = C⁻¹ := by rw [Matrix.nonsing_inv_mul E hE, Matrix.one_mul]
    have h := congrFun (congrFun hinvmul i) degree
    simpa only [E, C, Matrix.mul_apply, Matrix.vandermonde, Matrix.of_apply] using h
  rw [Matrix.mul_apply]
  let f := fun b : Bottom T => (NewtonE T)⁻¹ (fiberOrder T p.1 ri).1 b * RawM T b m
  change (∑ b, f b) = _
  rw [Fintype.sum_equiv (bottomFiberOrderEquiv T) f
    (fun x => f ((bottomFiberOrderEquiv T).symm x)) (fun b => by
      rw [(bottomFiberOrderEquiv T).symm_apply_apply])]
  dsimp only [f]
  simp only [Fintype.sum_sigma]
  change (∑ parent : Penultimate T, ∑ j,
      (NewtonE T)⁻¹ (fiberOrder T p.1 ri).1 (fiberOrder T parent j).1 *
        RawM T (fiberOrder T parent j).1 m) = _
  rw [Fintype.sum_eq_single p.1]
  · simp_rw [hsame, hRawM]
    calc
      (∑ j, (fiberEvaluation T p.1)⁻¹ ri j *
          (ancestorPrefix T p.1 m *
            T.label (Fin.last (n + 1)) (fiberOrder T p.1 j).1 ^
              (m.1 (Fin.last (n + 1))).val)) =
          ancestorPrefix T p.1 m *
            ∑ j, (fiberEvaluation T p.1)⁻¹ ri j *
              T.label (Fin.last (n + 1)) (fiberOrder T p.1 j).1 ^
                (m.1 (Fin.last (n + 1))).val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ancestorPrefix T p.1 m * (fiberCoefficient T p.1)⁻¹ ri
          ⟨(m.1 (Fin.last (n + 1))).val, he'⟩ := by
        congr 1
        simpa only [fiberValues] using hcoefficient ri
          ⟨(m.1 (Fin.last (n + 1))).val, he'⟩
  · intro parent hp
    apply Finset.sum_eq_zero
    intro j hj
    rw [hoff parent ri j hp.symm, zero_mul]

theorem NewtonPruningMatrix_blockTriangular {n : ℕ} (T : SourceTree (n + 2)) :
    (NewtonPruningMatrix T).BlockTriangular pruningDegree := by
  classical
  rintro ⟨r, p⟩ ⟨e, q⟩ her
  have herVal : e.1.val < r.1.val := her
  have he : e.1.val < Fintype.card (bottomFiber T p.1) :=
    herVal.trans p.2
  rw [NewtonPruningMatrix_apply_low T r e p q he]
  have hdegree (i : Fin (Fintype.card (bottomFiber T p.1))) :
      (fiberNewton T p.1 i.val).natDegree = i := by
    rw [fiberNewton, Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
    have hs : (Finset.univ.filter
        fun j : Fin (Fintype.card (bottomFiber T p.1)) => j.val < i.val) =
        Finset.Iio i := by
      ext j
      simp
    rw [hs, Fin.card_Iio]
  have hmonic (i : ℕ) : (fiberNewton T p.1 i).Monic := by
    apply Polynomial.monic_prod_of_monic
    intro j hj
    exact Polynomial.monic_X_sub_C _
  have hdet : (fiberCoefficient T p.1).det = 1 :=
    Matrix.det_matrixOfPolynomials (fun i => fiberNewton T p.1 i.val)
      hdegree (fun i => hmonic i.val)
  let _ : Invertible (fiberCoefficient T p.1) :=
    Matrix.invertibleOfIsUnitDet (fiberCoefficient T p.1)
      (by rw [hdet]; exact isUnit_one)
  have htri : (fiberCoefficient T p.1).BlockTriangular id :=
    Matrix.matrixOfPolynomials_blockTriangular
      (fun i => fiberNewton T p.1 i.val) (fun i => Nat.le_of_eq (hdegree i))
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular htri
  have herFin : (⟨e.1.val, he⟩ : Fin (Fintype.card (bottomFiber T p.1))) <
      ⟨r.1.val, p.2⟩ := herVal
  rw [hinv herFin, mul_zero]

/-- The literal rectangular source matrix made square by the recursively
proved bottom/column equivalence. -/
noncomputable def SourceSquare {L : ℕ} (T : SourceTree (L + 1)) :
    Matrix (Bottom T) (Bottom T) ℂ :=
  Matrix.reindex (Equiv.refl _) (bottomColumnEquiv T).symm (RawM T)

/-- The degree-`r` fiber in the common pruning index is exactly the bottom
level of the actual occupied pruning `T_r`. -/
noncomputable def pruningBlockEquiv {n : ℕ} (T : SourceTree (n + 2))
    (r : OccupiedDegree T) :
    {x : PruningIndex T // pruningDegree x = r} ≃
      Bottom (prune T r.1.val r.2) where
  toFun x := by
    rcases x with ⟨⟨e, p⟩, he⟩
    change e = r at he
    subst e
    exact (pruneBottomEquiv T r.1.val r.2).symm p
  invFun b :=
    ⟨⟨r, pruneBottomEquiv T r.1.val r.2 b⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨e, p⟩, he⟩
    change e = r at he
    subst e
    apply Subtype.ext
    apply Sigma.ext rfl
    rfl
  right_inv := by
    intro b
    exact (pruneBottomEquiv T r.1.val r.2).symm_apply_apply b

theorem NewtonPruningMatrix_diagonal_block_reindex {n : ℕ}
    (T : SourceTree (n + 2)) (r : OccupiedDegree T) :
    Matrix.reindex (pruningBlockEquiv T r) (pruningBlockEquiv T r)
        ((NewtonPruningMatrix T).toSquareBlock pruningDegree r) =
      SourceSquare (prune T r.1.val r.2) := by
  classical
  rw [Matrix.toSquareBlock_def]
  ext b c
  let p := pruneBottomEquiv T r.1.val r.2 b
  let q := pruneBottomEquiv T r.1.val r.2 c
  change NewtonPruningMatrix T ((pruningBlockEquiv T r).symm b).1
      ((pruningBlockEquiv T r).symm c).1 = SourceSquare (prune T r.1.val r.2) b c
  rw [show (pruningBlockEquiv T r).symm b = ⟨⟨r, p⟩, rfl⟩ from rfl]
  rw [show (pruningBlockEquiv T r).symm c = ⟨⟨r, q⟩, rfl⟩ from rfl]
  have hentry := NewtonPruningMatrix_apply_low T r r p q p.2
  have hdegree (i : Fin (Fintype.card (bottomFiber T p.1))) :
      (fiberNewton T p.1 i.val).natDegree = i := by
    rw [fiberNewton, Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
    have hs : (Finset.univ.filter
        fun j : Fin (Fintype.card (bottomFiber T p.1)) => j.val < i.val) =
        Finset.Iio i := by
      ext j
      simp
    rw [hs, Fin.card_Iio]
  have hmonic (i : ℕ) : (fiberNewton T p.1 i).Monic := by
    apply Polynomial.monic_prod_of_monic
    intro j hj
    exact Polynomial.monic_X_sub_C _
  let P := fiberCoefficient T p.1
  have hdet : IsUnit P.det := by
    have hdetEq : P.det = 1 := by
      dsimp only [P]
      exact Matrix.det_matrixOfPolynomials (fun i => fiberNewton T p.1 i.val)
        hdegree (fun i => hmonic i.val)
    rw [hdetEq]
    exact isUnit_one
  have htri : P.BlockTriangular id := by
    dsimp only [P]
    exact Matrix.matrixOfPolynomials_blockTriangular
      (fun i => fiberNewton T p.1 i.val) (fun i => Nat.le_of_eq (hdegree i))
  let _ : Invertible P := Matrix.invertibleOfIsUnitDet P hdet
  have hinv : P⁻¹.BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular htri
  have hdiag : P⁻¹ ⟨r.1.val, p.2⟩ ⟨r.1.val, p.2⟩ = 1 := by
    let e : Fin (Fintype.card (bottomFiber T p.1)) := ⟨r.1.val, p.2⟩
    have hmul := Matrix.nonsing_inv_mul P hdet
    have hentry' := congrFun (congrFun hmul e) e
    simp only [Matrix.mul_apply, Matrix.one_apply, if_pos] at hentry'
    have hpdiag : P e e = 1 := by
      dsimp only [P, fiberCoefficient, Matrix.of_apply]
      simpa only [hdegree] using (hmonic e.val).coeff_natDegree
    rw [Finset.sum_eq_single e] at hentry'
    · rw [hpdiag, mul_one] at hentry'
      exact hentry'
    · intro k hk hke
      rcases lt_or_gt_of_ne hke with hlt | hgt
      · rw [hinv hlt, zero_mul]
      · rw [htri hgt, mul_zero]
    · intro he
      exact (he (Finset.mem_univ e)).elim
  change (fiberCoefficient T p.1)⁻¹ _ _ = 1 at hdiag
  rw [hdiag, mul_one] at hentry
  rw [hentry]
  change ancestorPrefix T p.1
      (liftColumn T r.1.val r.2
        (bottomColumnEquiv (prune T r.1.val r.2)
          ((pruneBottomEquiv T r.1.val r.2).symm q))) = _
  have hprefix : ancestorPrefix T p.1
      (liftColumn T r.1.val r.2
        (bottomColumnEquiv (prune T r.1.val r.2)
          ((pruneBottomEquiv T r.1.val r.2).symm q))) =
      RawM (prune T r.1.val r.2)
        ((pruneBottomEquiv T r.1.val r.2).symm p)
        (bottomColumnEquiv (prune T r.1.val r.2)
          ((pruneBottomEquiv T r.1.val r.2).symm q)) := by
    simp only [ancestorPrefix, RawM]
    apply Finset.prod_congr rfl
    intro i hi
    change T.label i.castSucc _ ^
        ((liftColumn T r.1.val r.2
          (bottomColumnEquiv (prune T r.1.val r.2)
            ((pruneBottomEquiv T r.1.val r.2).symm q))).1 i.castSucc).val =
      T.label i.castSucc _ ^
        ((bottomColumnEquiv (prune T r.1.val r.2)
          ((pruneBottomEquiv T r.1.val r.2).symm q)).1 i).val
    have hexponent :
        ((liftColumn T r.1.val r.2
          (bottomColumnEquiv (prune T r.1.val r.2)
            ((pruneBottomEquiv T r.1.val r.2).symm q))).1 i.castSucc).val =
        ((bottomColumnEquiv (prune T r.1.val r.2)
          ((pruneBottomEquiv T r.1.val r.2).symm q)).1 i).val := by
      simp [liftColumn, liftExponents]
    rw [hexponent]
    rfl
  rw [hprefix]
  simp only [p, q, Equiv.symm_apply_apply, SourceSquare,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm,
    Equiv.coe_refl, Equiv.symm_symm, id_eq]

theorem det_NewtonPruningMatrix_blocks {n : ℕ} (T : SourceTree (n + 2)) :
    (NewtonPruningMatrix T).det =
      ∏ r : OccupiedDegree T, (SourceSquare (prune T r.1.val r.2)).det := by
  classical
  rw [(NewtonPruningMatrix_blockTriangular T).det_fintype]
  apply Fintype.prod_congr
  intro r
  rw [← Matrix.det_reindex_self (pruningBlockEquiv T r)]
  exact congrArg Matrix.det (NewtonPruningMatrix_diagonal_block_reindex T r)

/-- The sole permutation comparing the recursive column squaring with the
Newton row grouping. -/
noncomputable def pruningPermutation {n : ℕ} (T : SourceTree (n + 2)) :
    Equiv.Perm (PruningIndex T) :=
  (pruningColumnEquiv T).symm |>.trans
    ((bottomColumnEquiv T).symm.trans (pruningRowEquiv T))

/-- The occupied pruning recurrence with Mathlib-oriented sibling
Vandermonde determinants. -/
theorem sourceSquare_det_recurrence_mathlib {n : ℕ} (T : SourceTree (n + 2)) :
    (SourceSquare T).det =
      (↑(Equiv.Perm.sign (pruningPermutation T)) : ℂ) *
        (∏ p ∈ Finset.univ.image (bottomParent T),
          (Matrix.vandermonde (fiberValues T p)).det) *
        ∏ r : OccupiedDegree T,
          (SourceSquare (prune T r.1.val r.2)).det := by
  classical
  let s : ℂ := ↑(Equiv.Perm.sign (pruningPermutation T))
  let a : ℂ := (NewtonE T).det
  let ai : ℂ := ((NewtonE T)⁻¹).det
  let b : ℂ := (SourceSquare T).det
  let blocks : ℂ := ∏ r : OccupiedDegree T,
    (SourceSquare (prune T r.1.val r.2)).det
  have hsUnits : Equiv.Perm.sign (pruningPermutation T) *
      Equiv.Perm.sign (pruningPermutation T) = 1 := by
    rw [← Equiv.Perm.sign_inv (pruningPermutation T)]
    rw [← Equiv.Perm.sign_mul]
    simp
  have hsInt : (↑(Equiv.Perm.sign (pruningPermutation T)) : ℤ) *
      (↑(Equiv.Perm.sign (pruningPermutation T)) : ℤ) = 1 := by
    exact congrArg Units.val hsUnits
  have hs : s * s = 1 := by
    dsimp only [s]
    exact_mod_cast hsInt
  have ha : ai * a = 1 := by
    dsimp only [ai, a]
    exact Matrix.det_nonsing_inv_mul_det (NewtonE T)
      (isUnit_iff_ne_zero.mpr (det_NewtonE_ne_zero T))
  have hblocks : (NewtonPruningMatrix T).det = blocks := by
    exact det_NewtonPruningMatrix_blocks T
  have hsource : (NewtonPruningMatrix T).det = s * ai * b := by
    have hmatrix : NewtonPruningMatrix T =
        (Matrix.reindex (pruningRowEquiv T) (pruningRowEquiv T)
          ((NewtonE T)⁻¹ * SourceSquare T)).submatrix id (pruningPermutation T) := by
      ext i j
      simp only [NewtonPruningMatrix, SourceSquare, pruningPermutation,
        Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm,
        Equiv.coe_refl, id_eq, Equiv.trans_apply,
        Equiv.symm_apply_apply, Matrix.mul_apply]
    dsimp only [s, ai, b]
    rw [hmatrix, Matrix.det_permute', Matrix.det_reindex_self, Matrix.det_mul]
    ring
  have hproduct : blocks = s * ai * b := hblocks.symm.trans hsource
  change b = s * (∏ p ∈ Finset.univ.image (bottomParent T),
    (Matrix.vandermonde (fiberValues T p)).det) * blocks
  rw [← det_NewtonE]
  change b = s * a * blocks
  calc
    b = (s * s) * (ai * a) * b := by rw [hs, ha, one_mul, one_mul]
    _ = s * a * (s * ai * b) := by ring
    _ = s * a * blocks := by rw [← hproduct]

/-- The sibling Vandermonde orientation used in the source: the earlier
ordered sibling value minus the later one. -/
noncomputable def sourceSiblingVandermonde {n : ℕ} (T : SourceTree (n + 1))
    (p : Penultimate T) : ℂ :=
  ∏ i : Fin (Fintype.card (bottomFiber T p)),
    ∏ j ∈ Finset.Ioi i, (fiberValues T p i - fiberValues T p j)

/-- The integer unit converting Mathlib's `v_j - v_i` orientation to the
source's `v_i - v_j` orientation in one bottom fiber. -/
noncomputable def fiberOrientationSign {n : ℕ} (T : SourceTree (n + 1))
    (p : Penultimate T) : ℤ :=
  ∏ i : Fin (Fintype.card (bottomFiber T p)),
    ∏ _j ∈ Finset.Ioi i, (-1 : ℤ)

/-- The single integer sign accounting simultaneously for the column
permutation and every source/Mathlib Vandermonde orientation reversal. -/
noncomputable def pruningRecurrenceSign {n : ℕ} (T : SourceTree (n + 2)) : ℤ :=
  (Equiv.Perm.sign (pruningPermutation T) : ℤ) *
    ∏ p ∈ Finset.univ.image (bottomParent T), fiberOrientationSign T p

/-- Source-faithful occupied pruning recurrence.  The diagonal factors are
the literal square source matrices of the actual `T_r`, and the only unit is
the explicitly defined integer sign above. -/
theorem sourceSquare_det_pruning_recurrence {n : ℕ} (T : SourceTree (n + 2)) :
    (SourceSquare T).det =
      (pruningRecurrenceSign T : ℂ) *
        (∏ p ∈ Finset.univ.image (bottomParent T),
          sourceSiblingVandermonde T p) *
        ∏ r : OccupiedDegree T,
          (SourceSquare (prune T r.1.val r.2)).det := by
  classical
  have horientation (p : Penultimate T) :
      (Matrix.vandermonde (fiberValues T p)).det =
        (fiberOrientationSign T p : ℂ) * sourceSiblingVandermonde T p := by
    rw [Matrix.det_vandermonde]
    have hcast : (fiberOrientationSign T p : ℂ) =
        ∏ i : Fin (Fintype.card (bottomFiber T p)),
          ∏ _j ∈ Finset.Ioi i, (-1 : ℂ) := by
      simp [fiberOrientationSign]
    rw [hcast]
    simp only [sourceSiblingVandermonde]
    simp_rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro j hj
    ring
  rw [sourceSquare_det_recurrence_mathlib]
  simp_rw [horientation]
  rw [Finset.prod_mul_distrib]
  simp only [pruningRecurrenceSign, Int.cast_mul, Int.cast_prod]
  ring

#print axioms sourceSquare_det_pruning_recurrence

end D5.S3.Quantum.Algebra.DegeneracyGraphDeterminant
