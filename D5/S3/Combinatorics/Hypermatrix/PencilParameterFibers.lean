/- GID: D5/S3/Combinatorics/Hypermatrix/PencilParameterFibers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hypermatrix/PencilParameterFibers
   mirror-E: none(waiver:noncomputable-finite-field-enumeration)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic]
   utility: none
   digest: Full-rank pencils have explicit standard factors with scalar fibers. -/

import D5.S3.Combinatorics.Hypermatrix.MaskedFacesDefs
import D5.S3.Observer.Hankel.HankelRankMinimality

set_option autoImplicit false
open scoped BigOperators
open D5.S3.Combinatorics.Hypermatrix.MaskedFacesDefs

namespace D5.S3.Combinatorics.Hypermatrix.PencilParameterFibers

set_option maxHeartbeats 3000000 in
-- The proof combines induction and explicit finite coordinate constructions.
theorem pencil_parameter_fibers (F : Type*) [Field F]
    (k : ℕ) (hk : 1 ≤ k) :
    (∀ T : Faces F k, ClosureFullRank T →
      ∃ A : GL (Fin (k+1)) F, ∃ B : GL (Fin k) F,
        T.1 = A.val * E0 F k * B.val ∧ T.2 = A.val * E1 F k * B.val) ∧
    (∀ g : Factors F k, ClosureFullRank (factorMap g)) ∧
    (∀ (g : Factors F k) (u : Fˣ), factorMap (shift g u) = factorMap g) ∧
    (∀ g h : Factors F k, factorMap h = factorMap g → ∃ u : Fˣ, h = shift g u) ∧
    (∀ g : Factors F k, Function.Injective (shift g)) := by
  classical
  have rankInjective (M : Matrix (Fin (k + 1)) (Fin k) (AlgebraicClosure F))
      (hM : M.rank = k) : Function.Injective M.mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    have hr := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    change M.rank + Module.finrank (AlgebraicClosure F) M.mulVecLin.ker =
      Module.finrank (AlgebraicClosure F) (Fin k → AlgebraicClosure F) at hr
    simp only [hM, Module.finrank_pi, Fintype.card_fin] at hr
    omega
  have baseInjective (T : Faces F k) (hT : ClosureFullRank T) :
      Function.Injective T.1.mulVecLin := by
    have hm : (T.1.map (algebraMap F (AlgebraicClosure F))).rank = k := by
      simpa using hT 1 0 (Or.inl one_ne_zero)
    have hi := rankInjective _ hm
    intro x y hxy
    have he : (algebraMap F (AlgebraicClosure F)) ∘ x =
        (algebraMap F (AlgebraicClosure F)) ∘ y := by
      apply hi
      ext r
      simpa only [Matrix.mulVecLin_apply, ← RingHom.map_mulVec] using
        congrArg (algebraMap F (AlgebraicClosure F)) (congrFun hxy r)
    ext j
    exact (algebraMap F (AlgebraicClosure F)).injective (congrFun he j)
  have normalization (T : Faces F k) (hT : ClosureFullRank T) :
      ∃ A : GL (Fin (k + 1)) F, ∃ B : GL (Fin k) F,
        T.1 = (A : Matrix (Fin (k + 1)) (Fin (k + 1)) F) * E0 F k *
          (B : Matrix (Fin k) (Fin k) F) ∧
        T.2 = (A : Matrix (Fin (k + 1)) (Fin (k + 1)) F) * E1 F k *
          (B : Matrix (Fin k) (Fin k) F) := by
    have hcols : LinearIndependent F T.1.col :=
      Matrix.mulVec_injective_iff.mp (baseInjective T hT)
    have hfirst : ∃ A : GL (Fin (k + 1)) F,
        T.1 = (A : Matrix (Fin (k + 1)) (Fin (k + 1)) F) * E0 F k := by
      have hrange : Module.finrank F T.1.mulVecLin.range = k := by
        simpa using LinearMap.finrank_range_of_inj (baseInjective T hT)
      have hnotop : Submodule.span F (Set.range T.1.col) ≠ ⊤ := by
        intro htop
        rw [Matrix.range_mulVecLin, htop, finrank_top] at hrange
        simp only [Module.finrank_pi, Fintype.card_fin] at hrange
        omega
      obtain ⟨y, hy⟩ : ∃ y, y ∉ Submodule.span F (Set.range T.1.col) := by
        by_contra! hall
        apply hnotop
        ext y
        simp [hall y]
      let M : Matrix (Fin (k + 1)) (Fin (k + 1)) F :=
        fun r j => (Fin.snoc T.1.col y : Fin (k + 1) → (Fin (k + 1) → F)) j r
      have hM : LinearIndependent F M.col := hcols.finSnoc hy
      obtain ⟨A, hA⟩ := Matrix.linearIndependent_cols_iff_isUnit.mp hM
      refine ⟨A, ?_⟩
      rw [hA]
      ext r j
      change T.1 r j = ∑ t : Fin (k + 1), M r t * E0 F k t j
      simp [E0, M, Matrix.col]
      exact (congrFun (Fin.snoc_castSucc
        (α := fun _ => Fin (k + 1) → F) y T.1.col j) r).symm
    obtain ⟨A, hA⟩ := hfirst
    let S : Matrix (Fin (k + 1)) (Fin k) F :=
      A.inv * T.2
    let f := algebraMap F (AlgebraicClosure F)
    let Ai : GL (Fin (k + 1)) (AlgebraicClosure F) :=
      Matrix.GeneralLinearGroup.map f A⁻¹
    have hcancel : A.inv *
        (A : Matrix (Fin (k + 1)) (Fin (k + 1)) F) = 1 := by
      exact A.inv_val
    have hS : ∀ a b : AlgebraicClosure F, a ≠ 0 ∨ b ≠ 0 →
        (a • (E0 F k).map f + b • S.map f).rank = k := by
      intro a b hab
      have he : a • (E0 F k).map f + b • S.map f =
          (Ai : Matrix (Fin (k + 1)) (Fin (k + 1)) (AlgebraicClosure F)) *
            (a • T.1.map f + b • T.2.map f) := by
        change a • (E0 F k).map f + b • S.map f =
          A.inv.map f * (a • T.1.map f + b • T.2.map f)
        have hf0 : A.inv.map f * T.1.map f = (E0 F k).map f := by
          rw [hA, Matrix.map_mul, ← Matrix.mul_assoc, ← Matrix.map_mul, hcancel]
          simp
        have hf1 : A.inv.map f * T.2.map f = S.map f := by
          exact Matrix.map_mul.symm
        rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hf0, hf1]
      rw [he, Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units Ai)]
      exact hT a b hab
    let K := AlgebraicClosure F
    let CM : Matrix (Fin k) (Fin k) F := S.submatrix Fin.castSucc id
    let CF : Module.End F (Fin k → F) := CM.mulVecLin
    let C : Module.End K (Fin k → K) := (CM.map f).mulVecLin
    let ell : (Fin k → K) →ₗ[K] K :=
      (LinearMap.proj (Fin.last k)).comp (S.map f).mulVecLin
    let N := D5.S3.Observer.LinearMemory.ZeroMemoryCriterion.eventualKernel ell C
    have hNinv : ∀ v ∈ N, C v ∈ N :=
      D5.S3.Observer.LinearMemory.ZeroMemoryCriterion.eventualKernel_invariant ell C
    have hNell : N ≤ ell.ker :=
      D5.S3.Observer.LinearMemory.ZeroMemoryCriterion.eventualKernel_le_ker ell C
    have hNzero : N = ⊥ := by
      by_contra hN
      letI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN
      obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (C.restrict hNinv)
      obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
      have hv0 : (v : Fin k → K) ≠ 0 := by
        intro hz
        apply hv.2
        exact Subtype.ext hz
      have hve : C (v : Fin k → K) = c • (v : Fin k → K) := by
        exact congrArg (fun z : N => (z : Fin k → K)) hv.apply_eq_smul
      have hle : ell (v : Fin k → K) = 0 := LinearMap.mem_ker.mp (hNell v.property)
      let M : Matrix (Fin (k + 1)) (Fin k) K :=
        c • (E0 F k).map f + (-1 : K) • S.map f
      have hi := rankInjective M (hS c (-1) (Or.inr (neg_ne_zero.mpr one_ne_zero)))
      have hmzero : M.mulVec (v : Fin k → K) = 0 := by
        ext r
        refine Fin.lastCases ?_ (fun i => ?_) r
        · have hn : ∀ j : Fin k, Fin.last k ≠ j.castSucc := by
            intro j heq
            exact (Nat.ne_of_lt j.is_lt) (congrArg Fin.val heq).symm
          change (S.map f).mulVec (v : Fin k → K) (Fin.last k) = 0 at hle
          simp [M, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec,
            dotProduct, E0, Matrix.map_apply, hn, hle]
          try simp only [Matrix.mulVec, dotProduct, Matrix.map_apply] at hle
          calc
            (∑ j, -f (S (Fin.last k) j) * (v : Fin k → K) j) =
                ∑ j, -(f (S (Fin.last k) j) * (v : Fin k → K) j) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
            _ = -(∑ j, f (S (Fin.last k) j) * (v : Fin k → K) j) :=
              Finset.sum_neg_distrib (fun j : Fin k => f (S (Fin.last k) j) * (v : Fin k → K) j)
            _ = 0 := by rw [hle, neg_zero]
        · have hvi := congrFun hve i
          change ((S.map f).submatrix Fin.castSucc id).mulVec (v : Fin k → K) i =
            c * (v : Fin k → K) i at hvi
          simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq] at hvi
          simp [M, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec,
            dotProduct, E0, Matrix.map_apply, add_mul, Finset.sum_add_distrib,
            Finset.sum_neg_distrib, hvi]
          try simp only [Matrix.map_apply] at hvi
          have hz : c * (v : Fin k → K) i -
              (∑ j, f (S i.castSucc j) * (v : Fin k → K) j) = 0 := by
            rw [hvi]
            ring
          have hs : (∑ j, -f (S i.castSucc j) * (v : Fin k → K) j) =
              -(∑ j, f (S i.castSucc j) * (v : Fin k → K) j) := by
            calc
              _ = ∑ j, -(f (S i.castSucc j) * (v : Fin k → K) j) := by
                apply Finset.sum_congr rfl
                intro j _
                ring
              _ = _ := Finset.sum_neg_distrib (fun j : Fin k => f (S i.castSucc j) * (v : Fin k → K) j)
          rw [hs]
          simpa only [sub_eq_add_neg] using hz
      apply hv0
      apply hi
      simpa [Matrix.mulVecLin_apply] using hmzero
    let Obs := D5.S3.Observer.Hankel.HankelRankMinimality.finiteObservability C ell k
    have hObs : Obs.ker = ⊥ := by
      rw [D5.S3.Observer.Hankel.HankelRankMinimality.finiteObservability_ker_eq_eventualKernel C ell k (by simp)]
      exact hNzero
    let ellF : (Fin k → F) →ₗ[F] F :=
      (LinearMap.proj (Fin.last k)).comp S.mulVecLin
    let OF := D5.S3.Observer.Hankel.HankelRankMinimality.finiteObservability CF ellF k
    have transport (n : ℕ) (v : Fin k → F) :
        f ∘ ((CF ^ n) v) = (C ^ n) (f ∘ v) := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
        ext i
        exact RingHom.map_mulVec f CM ((CF ^ n) v) i
    have hOF : Function.Injective OF := by
      apply LinearMap.ker_eq_bot.mp
      apply le_antisymm
      · intro v hv
        have hz : Obs (f ∘ v) = 0 := by
          ext i
          change ell ((C ^ i.val) (f ∘ v)) = 0
          rw [← transport]
          change (S.map f).mulVec (f ∘ ((CF ^ i.val) v)) (Fin.last k) = 0
          rw [← RingHom.map_mulVec]
          have ho := congrFun (LinearMap.mem_ker.mp hv) i
          change S.mulVec ((CF ^ i.val) v) (Fin.last k) = 0 at ho
          rw [ho, map_zero]
        have hzero : f ∘ v = 0 := by
          have hm := LinearMap.mem_ker.mpr hz
          rw [hObs] at hm
          simpa using hm
        change v = 0
        ext i
        exact f.injective (by simpa using congrFun hzero i)
      · exact bot_le
    let obsEquiv := LinearEquiv.ofInjectiveEndo OF hOF
    let last : Fin k := ⟨k - 1, by omega⟩
    let x : Fin k → F := obsEquiv.symm ((Pi.single last (1 : F) : Fin k → F))
    have hx (i : Fin k) : ellF ((CF ^ i.val) x) = if i = last then 1 else 0 := by
      have he : OF x = (Pi.single last (1 : F) : Fin k → F) :=
        obsEquiv.apply_symm_apply ((Pi.single last (1 : F) : Fin k → F))
      have hi := congrFun he i
      change ellF ((CF ^ i.val) x) = ((Pi.single last (1 : F) : Fin k → F)) i at hi
      simpa only [Pi.single_apply, eq_comm] using hi
    let P : Matrix (Fin k) (Fin k) F := fun r j => ((CF ^ j.val) x) r
    let O : Matrix (Fin k) (Fin k) F := LinearMap.toMatrix' OF
    let D : Matrix (Fin k) (Fin k) F := (O * P).submatrix Fin.rev id
    have hD (i j : Fin k) : D i j = ellF ((CF ^ (i.rev.val + j.val)) x) := by
      change (O * P) i.rev j = _
      change O.mulVec ((CF ^ j.val) x) i.rev = _
      rw [LinearMap.toMatrix'_mulVec]
      change ellF ((CF ^ i.rev.val) ((CF ^ j.val) x)) = _
      rw [← Module.End.mul_apply, ← pow_add]
    have hupper : D.IsUpperTriangular := by
      intro i j hji
      rw [hD]
      have hn : i.rev.val + j.val < k - 1 := by
        simp only [Fin.val_rev]
        have hj : j.val < i.val := hji
        omega
      rw [hx ⟨i.rev.val + j.val, by omega⟩]
      split_ifs with he
      · have hv := congrArg Fin.val he
        change i.rev.val + j.val = k - 1 at hv
        exact False.elim ((Nat.ne_of_lt hn) hv)
      · rfl
    have hdiag (i : Fin k) : D i i = 1 := by
      rw [hD]
      have he : i.rev.val + i.val = k - 1 := by simp [Fin.val_rev]; omega
      rw [he]
      exact (hx last).trans (if_pos rfl)
    have hDdet : D.det = 1 := by
      rw [Matrix.det_of_isUpperTriangular hupper]
      simp [hdiag]
    have hPinj : Function.Injective P.mulVecLin := by
      have hDi : Function.Injective D.mulVecLin :=
        Matrix.mulVec_injective_iff.mpr
          (Matrix.linearIndependent_cols_iff_isUnit.mpr
            ((D.isUnit_iff_isUnit_det).mpr (by rw [hDdet]; exact isUnit_one)))
      intro z w hzw
      apply hDi
      ext i
      change (O * P).mulVec z i.rev = (O * P).mulVec w i.rev
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact congrFun (congrArg O.mulVec hzw) i.rev
    have hPcols : LinearIndependent F P.col := Matrix.mulVec_injective_iff.mp hPinj
    obtain ⟨Pg, hPg⟩ := Matrix.linearIndependent_cols_iff_isUnit.mp hPcols
    have hE0inj : Function.Injective (E0 F k).mulVecLin := by
      intro z w hzw
      ext j
      have he := congrFun hzw j.castSucc
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, E0] using he
    let w : Fin k → (Fin (k + 1) → F) := fun j => (E0 F k).mulVec (P.col j)
    let y : Fin (k + 1) → F := S.mulVec (P.col last)
    have hw : LinearIndependent F w :=
      hPcols.map' (E0 F k).mulVecLin (LinearMap.ker_eq_bot.mpr hE0inj)
    have hwlast (j : Fin k) : w j (Fin.last k) = 0 := by
      have hn : ∀ t : Fin k, Fin.last k ≠ t.castSucc := by
        intro t heq
        exact (Nat.ne_of_lt t.is_lt) (congrArg Fin.val heq).symm
      simp [w, E0, Matrix.mulVec, dotProduct, hn]
    have hylast : y (Fin.last k) = 1 := by
      exact (hx last).trans (if_pos rfl)
    have hy : y ∉ Submodule.span F (Set.range w) := by
      intro hy
      have hspan : Submodule.span F (Set.range w) ≤
          (LinearMap.proj (Fin.last k) : (Fin (k + 1) → F) →ₗ[F] F).ker := by
        apply Submodule.span_le.mpr
        rintro z ⟨j, rfl⟩
        exact LinearMap.mem_ker.mpr (hwlast j)
      have hz : y (Fin.last k) = 0 := LinearMap.mem_ker.mp (hspan hy)
      exact one_ne_zero (hylast.symm.trans hz)
    let Q : Matrix (Fin (k + 1)) (Fin (k + 1)) F :=
      fun r j => (Fin.snoc w y : Fin (k + 1) → (Fin (k + 1) → F)) j r
    have hQcols : LinearIndependent F Q.col := hw.finSnoc hy
    obtain ⟨Qg, hQg⟩ := Matrix.linearIndependent_cols_iff_isUnit.mp hQcols
    have hchain (j : Fin k) : Q.col j.succ = S.mulVec (P.col j) := by
      by_cases hj : j.val + 1 < k
      · let nxt : Fin k := ⟨j.val + 1, hj⟩
        have hs : j.succ = nxt.castSucc := Fin.ext rfl
        rw [hs]
        change (Fin.snoc w y : Fin (k + 1) → (Fin (k + 1) → F)) nxt.castSucc = _
        rw [Fin.snoc_castSucc]
        ext r
        refine Fin.lastCases ?_ (fun i => ?_) r
        · rw [hwlast]
          change 0 = ellF ((CF ^ j.val) x)
          rw [hx]
          have hne : j ≠ last := by intro he; have hh := congrArg Fin.val he; dsimp [last] at hh; omega
          simp [hne]
        · change (E0 F k).mulVec ((CF ^ nxt.val) x) i.castSucc =
            S.mulVec ((CF ^ j.val) x) i.castSucc
          have he : (E0 F k).mulVec ((CF ^ nxt.val) x) i.castSucc =
              ((CF ^ nxt.val) x) i := by simp [E0, Matrix.mulVec, dotProduct]
          rw [he]
          change ((CF ^ (j.val + 1)) x) i = (CF ((CF ^ j.val) x)) i
          rw [pow_succ', Module.End.mul_apply]
      · have hjlast : j = last := by apply Fin.ext; dsimp [last]; omega
        have hs : j.succ = Fin.last k := by apply Fin.ext; simp; omega
        rw [hs]
        change (Fin.snoc w y : Fin (k + 1) → (Fin (k + 1) → F)) (Fin.last k) = _
        rw [Fin.snoc_last, hjlast]
    have hQE0 : Q * E0 F k = E0 F k * P := by
      ext r j
      change (∑ t, Q r t * E0 F k t j) = (E0 F k).mulVec (P.col j) r
      simp only [E0, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      exact congrFun (Fin.snoc_castSucc (α := fun _ => Fin (k + 1) → F) y w j) r
    have hQE1 : Q * E1 F k = S * P := by
      ext r j
      change (∑ t, Q r t * E1 F k t j) = S.mulVec (P.col j) r
      simp only [E1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      exact congrFun (hchain j) r
    have hPcancel : P * Pg.inv = 1 := by rw [← hPg]; exact Pg.val_inv
    have hAS : (A : Matrix (Fin (k + 1)) (Fin (k + 1)) F) * S = T.2 := by
      change (A : Matrix (Fin (k + 1)) (Fin (k + 1)) F) * (A.inv * T.2) = T.2
      rw [← Matrix.mul_assoc, A.val_inv, Matrix.one_mul]
    refine ⟨A * Qg, Pg⁻¹, ?_, ?_⟩
    · change T.1 = ((A : Matrix (Fin (k + 1)) (Fin (k + 1)) F) * (Qg : Matrix (Fin (k + 1)) (Fin (k + 1)) F)) * E0 F k * Pg.inv
      rw [hQg, Matrix.mul_assoc (A : Matrix (Fin (k + 1)) (Fin (k + 1)) F) Q (E0 F k), hQE0]
      rw [← Matrix.mul_assoc (A : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (E0 F k) P]
      rw [Matrix.mul_assoc, hPcancel, Matrix.mul_one]
      exact hA
    · change T.2 = ((A : Matrix (Fin (k + 1)) (Fin (k + 1)) F) * (Qg : Matrix (Fin (k + 1)) (Fin (k + 1)) F)) * E1 F k * Pg.inv
      rw [hQg, Matrix.mul_assoc (A : Matrix (Fin (k + 1)) (Fin (k + 1)) F) Q (E1 F k), hQE1]
      rw [← Matrix.mul_assoc (A : Matrix (Fin (k + 1)) (Fin (k + 1)) F) S P]
      rw [Matrix.mul_assoc, hPcancel, Matrix.mul_one, hAS]

  have intertwinerScalar
      (U : Matrix (Fin (k + 1)) (Fin (k + 1)) F)
      (V : Matrix (Fin k) (Fin k) F)
      (h0 : U * E0 F k = E0 F k * V)
      (h1 : U * E1 F k = E1 F k * V) :
      ∃ c : F, U = c • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) ∧
        V = c • (1 : Matrix (Fin k) (Fin k) F) := by
    have h0entry (i j : Fin k) : U i.castSucc j.castSucc = V i j := by
      have h := congrFun (congrFun h0 i.castSucc) j
      simpa [Matrix.mul_apply, E0] using h
    have h1entry (i j : Fin k) : U i.succ j.succ = V i j := by
      have h := congrFun (congrFun h1 i.succ) j
      simpa [Matrix.mul_apply, E1] using h
    have hstep (i j : Fin k) : U i.succ j.succ = U i.castSucc j.castSucc :=
      (h1entry i j).trans (h0entry i j).symm
    have htop (j : Fin k) : U 0 j.succ = 0 := by
      have h := congrFun (congrFun h1 0) j
      have hn (t : Fin k) : (0 : Fin (k+1)) ≠ t.succ := by
        intro he
        have hv := congrArg Fin.val he
        simp at hv
      simpa [Matrix.mul_apply, E1, hn] using h
    have hbottom (j : Fin k) : U (Fin.last k) j.castSucc = 0 := by
      have h := congrFun (congrFun h0 (Fin.last k)) j
      have hn (t : Fin k) : Fin.last k ≠ t.castSucc := by
        intro he
        have hv := congrArg Fin.val he
        simp at hv
        omega
      simpa [Matrix.mul_apply, E0, hn] using h
    let c := U 0 0
    have hupper (s : Fin (k + 1)) : ∀ r : Fin (k + 1), r ≤ s →
        U r s = if r = s then c else 0 := by
      induction s using Fin.induction with
      | zero =>
        intro r hr
        have he : r = 0 := le_antisymm hr (Fin.zero_le r)
        subst r
        simp [c]
      | succ j ih =>
        intro r
        refine Fin.cases ?_ (fun i => ?_) r
        · intro hr
          simp [htop j, (Fin.succ_ne_zero j).symm]
        · intro hr
          rw [hstep]
          have hij : i.castSucc ≤ j.castSucc := by
            change i.val ≤ j.val
            change i.val + 1 ≤ j.val + 1 at hr
            omega
          simpa only [Fin.succ_inj, Fin.castSucc_inj] using ih i.castSucc hij
    have hlower (r : Fin (k + 1)) : ∀ s : Fin (k + 1), s < r → U r s = 0 := by
      induction r using Fin.reverseInduction with
      | last =>
        intro s
        refine Fin.lastCases ?_ (fun j => ?_) s
        · intro hs
          exact False.elim (lt_irrefl _ hs)
        · intro hs
          exact hbottom j
      | cast i ih =>
        intro s
        refine Fin.lastCases ?_ (fun j => ?_) s
        · intro hs
          have hh : (Fin.last k).val < i.castSucc.val := hs
          simp at hh
          omega
        · intro hs
          rw [← hstep]
          apply ih j.succ
          change j.val + 1 < i.val + 1
          change j.val < i.val at hs
          omega
    have hU : U = c • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) := by
      ext r s
      by_cases hrs : r ≤ s
      · simpa [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] using hupper s r hrs
      · have hne : r ≠ s := by intro he; subst s; exact hrs le_rfl
        simpa [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hne] using
          hlower r s (lt_of_not_ge hrs)
    refine ⟨c, hU, ?_⟩
    ext i j
    rw [← h0entry, hU]
    simp [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]

  let factors := GL (Fin (k + 1)) F × GL (Fin k) F
  let factorMap : factors → Faces F k := fun g =>
    ((g.1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) * E0 F k *
        (g.2 : Matrix (Fin k) (Fin k) F),
      (g.1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) * E1 F k *
        (g.2 : Matrix (Fin k) (Fin k) F))
  let shift : factors → Fˣ → factors := fun g u =>
    (g.1 * Matrix.GeneralLinearGroup.scalar (Fin (k + 1)) u,
      Matrix.GeneralLinearGroup.scalar (Fin k) u⁻¹ * g.2)
  have scalarMatrix {n : ℕ} (u : Fˣ) :
      (Matrix.GeneralLinearGroup.scalar (Fin n) u : Matrix (Fin n) (Fin n) F) =
        (u : F) • 1 := by
    ext i j
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.one_apply, smul_eq_mul]
  have shiftMap (g : factors) (u : Fˣ) : factorMap (shift g u) = factorMap g := by
    apply Prod.ext <;>
      dsimp only [factorMap, shift, Prod.fst, Prod.snd] <;>
      simp only [Units.val_mul, scalarMatrix, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.one_mul, smul_smul, Units.val_inv_eq_inv_val,
        mul_inv_cancel₀ (Units.ne_zero u), inv_mul_cancel₀ (Units.ne_zero u), one_smul]
  have sameFactors (g h : factors) (he : factorMap h = factorMap g) :
      ∃ u : Fˣ, h = shift g u := by
    let Ug : GL (Fin (k + 1)) F := g.1⁻¹ * h.1
    let Vg : GL (Fin k) F := g.2 * h.2⁻¹
    have hi (E : Matrix (Fin (k + 1)) (Fin k) F)
        (heq : (h.1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) * E *
          (h.2 : Matrix (Fin k) (Fin k) F) =
          (g.1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) * E *
          (g.2 : Matrix (Fin k) (Fin k) F)) :
        (Ug : Matrix (Fin (k + 1)) (Fin (k + 1)) F) * E =
          E * (Vg : Matrix (Fin k) (Fin k) F) := by
      change (g.1.inv * (h.1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F)) * E =
        E * ((g.2 : Matrix (Fin k) (Fin k) F) * h.2.inv)
      calc
        _ = g.1.inv * ((h.1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) * E *
            (h.2 : Matrix (Fin k) (Fin k) F)) * h.2.inv := by
          simp [Matrix.mul_assoc, h.2.val_inv]
        _ = g.1.inv * ((g.1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) * E *
            (g.2 : Matrix (Fin k) (Fin k) F)) * h.2.inv := by rw [heq]
        _ = _ := by
          rw [← Matrix.mul_assoc g.1.inv, ← Matrix.mul_assoc g.1.inv,
            g.1.inv_val, Matrix.one_mul, Matrix.mul_assoc]
    obtain ⟨c, hcU, hcV⟩ := intertwinerScalar
      (Ug : Matrix (Fin (k + 1)) (Fin (k + 1)) F)
      (Vg : Matrix (Fin k) (Fin k) F)
      (hi (E0 F k) (congrArg Prod.fst he))
      (hi (E1 F k) (congrArg Prod.snd he))
    have hc : c ≠ 0 := by
      intro hc
      have hz : (Ug : Matrix (Fin (k + 1)) (Fin (k + 1)) F) = 0 := by
        simpa [hc] using hcU
      have hh := Ug.val_inv
      rw [hz, Matrix.zero_mul] at hh
      have he0 := congrFun (congrFun hh 0) 0
      exact (zero_ne_one : (0 : F) ≠ 1) (by simpa using he0)
    let u : Fˣ := Units.mk0 c hc
    have hUg : Ug = Matrix.GeneralLinearGroup.scalar (Fin (k + 1)) u := by
      apply Units.ext
      rw [scalarMatrix]
      exact hcU
    have hVg : Vg = Matrix.GeneralLinearGroup.scalar (Fin k) u := by
      apply Units.ext
      rw [scalarMatrix]
      exact hcV
    refine ⟨u, Prod.ext ?_ ?_⟩
    · change h.1 = g.1 * Matrix.GeneralLinearGroup.scalar (Fin (k + 1)) u
      rw [← hUg]
      simp [Ug, mul_assoc]
    · change h.2 = Matrix.GeneralLinearGroup.scalar (Fin k) u⁻¹ * g.2
      rw [map_inv, ← hVg]
      simp [Vg, mul_assoc]
  have shiftInjective (g : factors) : Function.Injective (shift g) := by
    intro u v huv
    have hs : Matrix.GeneralLinearGroup.scalar (Fin (k + 1)) u =
        Matrix.GeneralLinearGroup.scalar (Fin (k + 1)) v :=
      mul_left_cancel (congrArg Prod.fst huv)
    apply Units.ext
    have he := congrArg (fun G : GL (Fin (k + 1)) F => G 0 0) hs
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using he
  have standardFullRank : ClosureFullRank (E0 F k, E1 F k) := by
    intro a b hab
    let M : Matrix (Fin (k + 1)) (Fin k) (AlgebraicClosure F) :=
      a • (E0 F k).map (algebraMap F (AlgebraicClosure F)) +
        b • (E1 F k).map (algebraMap F (AlgebraicClosure F))
    change M.rank = k
    apply le_antisymm
    · simpa using M.rank_le_card_width
    · by_cases ha : a ≠ 0
      · let D := M.submatrix Fin.castSucc id
        have htri : D.IsLowerTriangular := by
          intro i j hij
          have hne0 : i.castSucc ≠ j.castSucc := by
            intro he
            have hh := congrArg Fin.val he
            change i.val = j.val at hh
            change i.val < j.val at hij
            omega
          have hne1 : i.castSucc ≠ j.succ := by
            intro he
            have hh := congrArg Fin.val he
            change i.val = j.val + 1 at hh
            change i.val < j.val at hij
            omega
          simp [D, M, E0, E1, Matrix.submatrix_apply, Matrix.map_apply, hne0, hne1]
        have hdiag (i : Fin k) : D i i = a := by
          have hn : i.castSucc ≠ i.succ := by
            intro he
            have hh := congrArg Fin.val he
            simp at hh
          simp [D, M, E0, E1, hn]
        have hdet : D.det ≠ 0 := by
          rw [Matrix.det_of_isLowerTriangular D htri]
          simp only [hdiag, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          exact pow_ne_zero k ha
        have hr : D.rank = k := by simpa using Matrix.rank_of_det_ne_zero hdet
        exact hr.ge.trans (Matrix.rank_submatrix_le M Fin.castSucc id)
      · have ha0 : a = 0 := not_ne_iff.mp ha
        have hb : b ≠ 0 := hab.resolve_left ha
        let D := M.submatrix Fin.succ id
        have htri : D.IsUpperTriangular := by
          intro i j hij
          have hn : i.succ ≠ j.succ := by
            intro he
            have hh := Fin.succ_inj.mp he
            subst j
            exact lt_irrefl _ hij
          simp [D, M, E0, E1, ha0, hn]
        have hdiag (i : Fin k) : D i i = b := by
          simp [D, M, E0, E1, ha0]
        have hdet : D.det ≠ 0 := by
          rw [Matrix.det_of_isUpperTriangular htri]
          simp only [hdiag, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          exact pow_ne_zero k hb
        have hr : D.rank = k := by simpa using Matrix.rank_of_det_ne_zero hdet
        exact hr.ge.trans (Matrix.rank_submatrix_le M Fin.succ id)
  have factorFullRank (g : factors) : ClosureFullRank (factorMap g) := by
    intro a b hab
    let f := algebraMap F (AlgebraicClosure F)
    let Ag := Matrix.GeneralLinearGroup.map f g.1
    let Bg := Matrix.GeneralLinearGroup.map f g.2
    have he : a • (factorMap g).1.map f + b • (factorMap g).2.map f =
        (Ag : Matrix (Fin (k + 1)) (Fin (k + 1)) (AlgebraicClosure F)) *
          (a • (E0 F k).map f + b • (E1 F k).map f) *
          (Bg : Matrix (Fin k) (Fin k) (AlgebraicClosure F)) := by
      change a • ((g.1 : Matrix (Fin (k+1)) (Fin (k+1)) F) * E0 F k *
          (g.2 : Matrix (Fin k) (Fin k) F)).map f +
        b • ((g.1 : Matrix (Fin (k+1)) (Fin (k+1)) F) * E1 F k *
          (g.2 : Matrix (Fin k) (Fin k) F)).map f =
        (g.1 : Matrix (Fin (k+1)) (Fin (k+1)) F).map f *
          (a • (E0 F k).map f + b • (E1 F k).map f) *
          (g.2 : Matrix (Fin k) (Fin k) F).map f
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_assoc]
    rw [he, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units Bg),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units Ag)]
    exact standardFullRank a b hab

  exact ⟨normalization, factorFullRank, shiftMap, sameFactors, shiftInjective⟩

end D5.S3.Combinatorics.Hypermatrix.PencilParameterFibers
