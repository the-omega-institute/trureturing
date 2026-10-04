/- GID: D5/S3/Combinatorics/Hypermatrix/SoutheastFactorization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hypermatrix/SoutheastFactorization
   mirror-E: none(waiver:noncomputable-finite-field-enumeration)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic]
   utility: none
   digest: Upper triangular factorization into unique southeast pivot cells. -/

import D5.S3.Combinatorics.Hypermatrix.MaskedFacesDefs

set_option autoImplicit false
open scoped BigOperators
open D5.S3.Combinatorics.Hypermatrix.MaskedFacesDefs

namespace D5.S3.Combinatorics.Hypermatrix.SoutheastFactorization

set_option maxHeartbeats 3000000 in
-- The proof combines induction and explicit finite coordinate constructions.
theorem southeast_factorization (F : Type*) [Field F] :
    (∀ (n : ℕ) (G : GL (Fin (n+1)) F),
        ∃ p : Fin (n+1), ∃ L C : GL (Fin (n+1)) F, ∃ D : GL (Fin n) F,
          L.val.IsUpperTriangular ∧ G = L * C ∧
          (∀ r, C.val r 0 = if r = p then 1 else 0) ∧
          D.val = C.val.submatrix p.succAbove Fin.succ ∧
          G.val p 0 ≠ 0 ∧ (∀ r, p < r → G.val r 0 = 0)) ∧
    (∀ (n : ℕ),
∀ G : GL (Fin n) F,
        ∃ U B : GL (Fin n) F, ∃ sigma : Equiv.Perm (Fin n),
          U.val.IsUpperTriangular ∧ G = U * B ∧
            (∀ a b, B.val (sigma a) b = if a = b then 1 else
              if a < b ∧ sigma b < sigma a then B.val (sigma a) b else 0)) ∧
    (∀ (n : ℕ) (sigma tau : Equiv.Perm (Fin n))
        (A C U : GL (Fin n) F) (hU : U.val.IsUpperTriangular)
        (hA : ∀ a b, A.val (sigma a) b = if a = b then 1 else
          if a < b ∧ sigma b < sigma a then A.val (sigma a) b else 0)
        (hC : ∀ a b, C.val (tau a) b = if a = b then 1 else
          if a < b ∧ tau b < tau a then C.val (tau a) b else 0)
        (hAC : A = U * C),
sigma = tau ∧ A = C ∧ U = 1) := by
  classical
  have upperPivotStep (n : ℕ) (G : GL (Fin (n+1)) F) :
      ∃ p : Fin (n+1), ∃ L C : GL (Fin (n+1)) F, ∃ D : GL (Fin n) F,
        L.val.IsUpperTriangular ∧ G = L * C ∧
        (∀ r, C.val r 0 = if r = p then 1 else 0) ∧
        D.val = C.val.submatrix p.succAbove Fin.succ ∧
        G.val p 0 ≠ 0 ∧ (∀ r, p < r → G.val r 0 = 0) := by
    let support : Finset (Fin (n+1)) := Finset.univ.filter (fun r => G.val r 0 ≠ 0)
    have hs : support.Nonempty := by
      by_contra hn
      have hz : ∀ r, G.val r 0 = 0 := by
        intro r
        by_contra hr
        exact hn ⟨r, by simp [support, hr]⟩
      have hd := Matrix.det_eq_zero_of_column_eq_zero 0 hz
      exact (isUnit_iff_ne_zero.mp (Matrix.isUnits_det_units G)) hd
    obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image support id hs
    have hpn : G.val p 0 ≠ 0 := by simpa [support] using hp
    have hbelow (r : Fin (n+1)) (hr : p < r) : G.val r 0 = 0 := by
      by_contra hnr
      have hh := hmax r (by simp [support, hnr])
      exact (not_le_of_gt hr) hh
    let Lm : Matrix (Fin (n+1)) (Fin (n+1)) F :=
      fun r j => if j = p then G.val r 0 else if r = j then 1 else 0
    have hupper : Lm.IsUpperTriangular := by
      intro r j hjr
      by_cases hj : j = p
      · subst j
        simp only [Lm, if_pos rfl]
        exact hbelow r hjr
      · have hrj : r ≠ j := ne_of_gt hjr
        simp [Lm, hj, hrj]
    have hdiag (r : Fin (n+1)) : Lm r r = if r = p then G.val p 0 else 1 := by
      by_cases hr : r = p
      · subst r; simp [Lm]
      · simp [Lm, hr]
    have hdet : Lm.det = G.val p 0 := by
      rw [Matrix.det_of_isUpperTriangular hupper]
      simp_rw [hdiag]
      simp
    have hunit : IsUnit Lm :=
      (Matrix.isUnit_iff_isUnit_det Lm).mpr (isUnit_iff_ne_zero.mpr (hdet ▸ hpn))
    let L : GL (Fin (n+1)) F := hunit.unit
    have hLv : L.val = Lm := IsUnit.unit_spec hunit
    let C : GL (Fin (n+1)) F := L⁻¹ * G
    have hcol (r : Fin (n+1)) : C.val r 0 = if r = p then 1 else 0 := by
      have hLc (t : Fin (n+1)) : L.val t p = G.val t 0 := by
        rw [hLv]; simp [Lm]
      change (∑ t, (L⁻¹).val r t * G.val t 0) = _
      simp_rw [← hLc]
      change ((L⁻¹).val * L.val) r p = _
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      simp [Matrix.one_apply]
    let Dm := C.val.submatrix p.succAbove Fin.succ
    have hminor : IsUnit Dm := by
      apply (Matrix.isUnit_iff_isUnit_det Dm).mpr
      apply isUnit_iff_ne_zero.mpr
      intro hd
      have hc : C.val.det = (-1 : F)^p.val * Dm.det := by
        rw [Matrix.det_succ_column_zero]
        simp_rw [hcol]
        simp [Dm]
      have hc0 : C.val.det = 0 := by rw [hc, hd, mul_zero]
      exact (isUnit_iff_ne_zero.mp (Matrix.isUnits_det_units C)) hc0
    refine ⟨p, L, C, hminor.unit, ?_, ?_, hcol, IsUnit.unit_spec hminor, hpn, hbelow⟩
    · simpa only [hLv] using hupper
    · simp [C]

  have leftSEExists (n : ℕ) : ∀ G : GL (Fin n) F,
      ∃ U B : GL (Fin n) F, ∃ sigma : Equiv.Perm (Fin n),
        U.val.IsUpperTriangular ∧ G = U * B ∧
          (∀ a b, B.val (sigma a) b = if a = b then 1 else
            if a < b ∧ sigma b < sigma a then B.val (sigma a) b else 0) := by
    induction n with
    | zero =>
      intro G
      refine ⟨1, 1, Equiv.refl _, ?_, ?_, ?_⟩
      · intro r
        exact Fin.elim0 r
      · apply Units.ext
        ext r
        exact Fin.elim0 r
      · intro a
        exact Fin.elim0 a
    | succ n ih =>
      intro G
      obtain ⟨p, L, C, D, hL, hG, hC, hD, hp, hbelow⟩ := upperPivotStep n G
      obtain ⟨U, B, tau, hU, hDB, hB⟩ := ih D
      let sigma : Equiv.Perm (Fin (n+1)) :=
        (finSuccEquiv' 0).trans ((Equiv.optionCongr tau).trans (finSuccEquiv' p).symm)
      have hs0 : sigma 0 = p := by simp [sigma]
      have hss (b : Fin n) : sigma b.succ = p.succAbove (tau b) := by
        have hz : finSuccEquiv' (0 : Fin (n+1)) b.succ = some b := by
          simpa only [Fin.succAbove_zero_apply] using
            finSuccEquiv'_succAbove (0 : Fin (n+1)) b
        change (finSuccEquiv' p).symm ((Equiv.optionCongr tau)
          ((finSuccEquiv' 0) b.succ)) = _
        rw [hz]
        rfl
      let c : Fin n → F := fun b => C.val p b.succ
      let alpha : Fin n → F := Matrix.vecMul c (B⁻¹).val
      let rho : Fin n → F := fun b => ∑ a : Fin n,
        if p.succAbove a < p then alpha a * B.val a b else 0
      have hBzero (a b : Fin n) (ha : p.succAbove a < p)
          (hb : p < p.succAbove (tau b)) : B.val a b = 0 := by
        have hh := hB (tau.symm a) b
        simp only [Equiv.apply_symm_apply] at hh
        have he : tau.symm a ≠ b := by
          intro he
          have hae : a = tau b := by simpa using congrArg tau he
          rw [hae] at ha
          exact (not_lt_of_ge (le_of_lt hb)) ha
        have hinv : ¬(tau.symm a < b ∧ tau b < a) := by
          rintro ⟨_, hab⟩
          have hba := (Fin.strictMono_succAbove p) hab
          exact (not_lt_of_ge (le_of_lt hb)) (hba.trans ha)
        simpa [he, hinv] using hh
      have hRowAllowed (b : Fin n) (hb : ¬ p.succAbove (tau b) < p) : rho b = 0 := by
        have hneq : p.succAbove (tau b) ≠ p := p.succAbove_ne (tau b)
        have hpb : p < p.succAbove (tau b) := lt_of_le_of_ne (le_of_not_gt hb) hneq.symm
        apply Finset.sum_eq_zero
        intro a _
        by_cases ha : p.succAbove a < p
        · simp [ha, hBzero a b ha hpb]
        · simp [ha]
      have hRowDecomposition (b : Fin n) :
          c b = rho b + ∑ a : Fin n,
            if p < p.succAbove a then alpha a * B.val a b else 0 := by
        have hfull : Matrix.vecMul alpha B.val = c := by
          dsimp [alpha]
          rw [Matrix.vecMul_vecMul]
          change Matrix.vecMul c ((B⁻¹ * B).val) = c
          simp
        have he := congrFun hfull b
        change (∑ a, alpha a * B.val a b) = c b at he
        rw [← he]
        dsimp [rho]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        rcases lt_or_gt_of_ne (p.succAbove_ne a) with ha | ha <;> simp [ha, not_lt_of_gt ha]
      let Am : Matrix (Fin (n+1)) (Fin (n+1)) F :=
        p.insertNth (Fin.cons 1 rho) (fun a => Fin.cons 0 (B.val a))
      have ha0 (r : Fin (n+1)) : Am r 0 = if r = p then 1 else 0 := by
        refine Fin.succAboveCases p ?_ (fun a => ?_) r
        · simp [Am]
        · simp [Am, p.succAbove_ne a]
      have haMinor : Am.submatrix p.succAbove Fin.succ = B.val := by
        ext a b
        change Am (p.succAbove a) b.succ = B.val a b
        simp [Am]
      have haShape :
          (∀ a b, Am (sigma a) b = if a = b then 1 else
            if a < b ∧ sigma b < sigma a then Am (sigma a) b else 0) := by
        intro a b
        refine Fin.cases ?_ (fun a => ?_) a
        · rw [hs0]
          refine Fin.cases ?_ (fun b => ?_) b
          · simp [Am]
          · rw [hss]
            have hb0 : (0 : Fin (n+1)) ≠ b.succ := Ne.symm (Fin.succ_ne_zero b)
            by_cases hb : p.succAbove (tau b) < p
            · simp [Am, hb, hb0]
            · simp [Am, hb, hRowAllowed b hb, hb0]
        · rw [hss]
          refine Fin.cases ?_ (fun b => ?_) b
          · simp [Am]
          · rw [hss]
            simpa [Am, Fin.succAbove_lt_succAbove_iff] using hB a b
      have haUnit : IsUnit Am := by
        apply (Matrix.isUnit_iff_isUnit_det Am).mpr
        apply isUnit_iff_ne_zero.mpr
        have hd : Am.det = (-1 : F)^p.val * B.val.det := by
          rw [Matrix.det_succ_column_zero]
          simp_rw [ha0]
          simp [haMinor]
        rw [hd]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
          (isUnit_iff_ne_zero.mp (Matrix.isUnits_det_units B))
      let Lm : Matrix (Fin (n+1)) (Fin (n+1)) F :=
        p.insertNth (p.insertNth 1 (fun a => if p < p.succAbove a then alpha a else 0))
          (fun a => p.insertNth 0 (U.val a))
      have hLmUpper : Lm.IsUpperTriangular := by
        intro r
        refine Fin.succAboveCases p ?_ (fun a => ?_) r
        · intro j
          refine Fin.succAboveCases p ?_ (fun b => ?_) j
          · intro hjr
            exact False.elim (lt_irrefl p hjr)
          · intro hjr
            change p.succAbove b < p at hjr
            have hnot : ¬p < p.succAbove b := not_lt_of_gt hjr
            simp [Lm, hnot]
        · intro j
          refine Fin.succAboveCases p ?_ (fun b => ?_) j
          · intro _
            simp [Lm]
          · intro hjr
            have hba : b < a := Fin.succAbove_lt_succAbove_iff.mp hjr
            simpa [Lm] using hU hba
      have hLmUnit : IsUnit Lm := by
        apply (Matrix.isUnit_iff_isUnit_det Lm).mpr
        apply isUnit_iff_ne_zero.mpr
        rw [Matrix.det_of_isUpperTriangular hLmUpper]
        apply Finset.prod_ne_zero_iff.mpr
        intro r _
        refine Fin.succAboveCases p ?_ (fun a => ?_) r
        · simp [Lm]
        · have hu := isUnit_iff_ne_zero.mp (Matrix.isUnits_det_units U)
          rw [Matrix.det_of_isUpperTriangular hU] at hu
          simpa [Lm] using Finset.prod_ne_zero_iff.mp hu a (Finset.mem_univ a)
      have hproduct : Lm * Am = C.val := by
        ext r j
        refine Fin.cases ?_ (fun b => ?_) j
        · rw [Matrix.mul_apply]
          simp_rw [ha0]
          change (∑ t : Fin (n+1), Lm r t * (if t = p then 1 else 0)) = C.val r 0
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          rw [hC]
          refine Fin.succAboveCases p ?_ (fun a => ?_) r
          · simp [Lm]
          · simp [Lm, p.succAbove_ne a]
        · rw [Matrix.mul_apply, Fin.sum_univ_succAbove _ p]
          refine Fin.succAboveCases p ?_ (fun a => ?_) r
          · simpa [Lm, Am, c, mul_comm] using (hRowDecomposition b).symm
          · have he := congrFun (congrFun (congrArg (fun V : GL (Fin n) F => V.val) hDB) a) b
            rw [hD] at he
            simpa [Lm, Am, Matrix.mul_apply, Matrix.submatrix_apply] using he.symm
      let A : GL (Fin (n+1)) F := haUnit.unit
      let L' : GL (Fin (n+1)) F := hLmUnit.unit
      have hAv : A.val = Am := IsUnit.unit_spec haUnit
      have hLv : L'.val = Lm := IsUnit.unit_spec hLmUnit
      have hL' : L'.val.IsUpperTriangular := by
        simpa only [hLv] using hLmUpper
      have hCA : C = L' * A := by
        apply Units.ext
        simpa only [Units.val_mul, hLv, hAv] using hproduct.symm
      refine ⟨L * L', A, sigma, ?_, ?_, ?_⟩
      · exact hL.mul hL'
      · rw [hG, hCA, mul_assoc]
      · simpa only [hAv] using haShape

  have seUnique (n : ℕ) (sigma tau : Equiv.Perm (Fin n))
      (A C U : GL (Fin n) F) (hU : U.val.IsUpperTriangular)
      (hA : ∀ a b, A.val (sigma a) b = if a = b then 1 else
        if a < b ∧ sigma b < sigma a then A.val (sigma a) b else 0)
      (hC : ∀ a b, C.val (tau a) b = if a = b then 1 else
        if a < b ∧ tau b < tau a then C.val (tau a) b else 0)
      (hAC : A = U * C) : sigma = tau ∧ A = C ∧ U = 1 := by
    have entryZero (p : Equiv.Perm (Fin n)) (M : GL (Fin n) F)
        (hM : ∀ a b, M.val (p a) b = if a = b then 1 else
          if a < b ∧ p b < p a then M.val (p a) b else 0)
        (r b : Fin n) (h : b < p.symm r ∨ r < p b) : M.val r b = 0 := by
      have hh := hM (p.symm r) b
      simp only [Equiv.apply_symm_apply] at hh
      rcases h with h | h
      · simpa [ne_of_gt h, not_lt_of_gt h] using hh
      · have hn : p.symm r ≠ b := by
          intro he
          have := congrArg p he
          simp only [Equiv.apply_symm_apply] at this
          exact (ne_of_lt h) this
        simpa [hn, not_lt_of_gt h] using hh
    have pivotOne (p : Equiv.Perm (Fin n)) (M : GL (Fin n) F)
        (hM : ∀ a b, M.val (p a) b = if a = b then 1 else
          if a < b ∧ p b < p a then M.val (p a) b else 0)
        (r : Fin n) : M.val r (p.symm r) = 1 := by
      simpa using hM (p.symm r) (p.symm r)
    have hdiag (r : Fin n) : U.val r r ≠ 0 := by
      have hd := isUnit_iff_ne_zero.mp (Matrix.isUnits_det_units U)
      rw [Matrix.det_of_isUpperTriangular hU] at hd
      exact Finset.prod_ne_zero_iff.mp hd r (Finset.mem_univ r)
    have he (r b : Fin n) : A.val r b = ∑ t : Fin n, U.val r t * C.val t b := by
      rw [hAC, Units.val_mul, Matrix.mul_apply]
    have rows (d : ℕ) : ∀ r : Fin n, n - r.val = d →
        sigma.symm r = tau.symm r ∧ (∀ b, A.val r b = C.val r b) ∧
          (∀ t, r < t → U.val r t = 0) := by
      induction d using Nat.strong_induction_on with
      | h d ih =>
        intro r hr
        have prior (s : Fin n) (hrs : r < s) : sigma.symm s = tau.symm s := by
          exact (ih (n-s.val) (by omega) s rfl).1
        have coeff (e : ℕ) : ∀ s : Fin n, n - s.val = e → r < s → U.val r s = 0 := by
          induction e using Nat.strong_induction_on with
          | h e ihs =>
            intro s hs hrs
            have hz : A.val r (tau.symm s) = 0 := by
              rw [← prior s hrs]
              apply entryZero sigma A hA
              right
              simpa using hrs
            have hc : (∑ t : Fin n, U.val r t * C.val t (tau.symm s)) = U.val r s := by
              rw [Finset.sum_eq_single s]
              · rw [pivotOne tau C hC, mul_one]
              · intro t _ hts
                rcases lt_or_gt_of_ne hts with ht | ht
                · rw [entryZero tau C hC t (tau.symm s) (Or.inr (by simpa using ht)), mul_zero]
                · rw [ihs (n-t.val) (by omega) t rfl (hrs.trans ht), zero_mul]
              · simp
            rw [he, hc] at hz
            exact hz
        have hcoeff (t : Fin n) (hrt : r < t) : U.val r t = 0 :=
          coeff (n-t.val) t rfl hrt
        have scale (b : Fin n) : A.val r b = U.val r r * C.val r b := by
          rw [he, Finset.sum_eq_single r]
          · intro t _ htr
            rcases lt_or_gt_of_ne htr with ht | ht
            · rw [hU ht, zero_mul]
            · rw [hcoeff t ht, zero_mul]
          · simp
        have hp : sigma.symm r = tau.symm r := by
          by_contra hn
          rcases lt_or_gt_of_ne hn with hlt | hgt
          · have hh := scale (sigma.symm r)
            rw [pivotOne sigma A hA,
              entryZero tau C hC r (sigma.symm r) (Or.inl hlt), mul_zero] at hh
            exact one_ne_zero hh
          · have hh := scale (tau.symm r)
            rw [entryZero sigma A hA r (tau.symm r) (Or.inl hgt),
              pivotOne tau C hC, mul_one] at hh
            exact hdiag r hh.symm
        have hd : U.val r r = 1 := by
          have hh := scale (tau.symm r)
          rw [← hp, pivotOne sigma A hA] at hh
          rw [hp, pivotOne tau C hC, mul_one] at hh
          exact hh.symm
        exact ⟨hp, fun b => by rw [scale, hd, one_mul], hcoeff⟩
    have hp : sigma = tau := by
      apply Equiv.ext
      intro a
      have hh := (rows (n-(sigma a).val) (sigma a) rfl).1
      have ht := congrArg tau hh
      simpa using ht.symm
    have hm : A = C := by
      apply Units.ext
      ext r b
      exact (rows (n-r.val) r rfl).2.1 b
    refine ⟨hp, hm, ?_⟩
    have hh : U * C = 1 * C := by rw [← hAC, hm, one_mul]
    exact mul_right_cancel hh

  exact ⟨upperPivotStep, leftSEExists, seUnique⟩

end D5.S3.Combinatorics.Hypermatrix.SoutheastFactorization
