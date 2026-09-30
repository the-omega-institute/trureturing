/- GID: D5/S3/Analytic/Dilation/ActualRegularLedgerCollision
   generality: G
   mirror-B: D5/B/S3/Analytic/Dilation/ActualRegularLedgerCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group representation ledgers share a formal-log history on one conjugacy class while differing in a raw grade. -/

import Mathlib
import D5.S3.Analytic.Dilation.EquivariantSeriesObserver
import D5.S3.Analytic.Dilation.MonsterPrimitiveMobiusRecovery

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Dilation.ActualRegularLedgerCollision

open scoped Polynomial
open PowerSeries
open Equiv Equiv.Perm
open D5.S3.Analytic.Dilation.EquivariantSeriesObserver

noncomputable section

theorem single_cycle_det (r : ℕ) (hr : 0 < r) :
    Matrix.det (1 - (Polynomial.X : ℚ[X]) • ((finRotate r).permMatrix ℚ[X])) =
      1 - Polynomial.X ^ r := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  let P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ[X] :=
    (finRotate (n + 1)).permMatrix ℚ[X]
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ[X] :=
    1 - (Polynomial.X : ℚ[X]) • P
  let c : Fin (n + 1) → ℚ[X] := fun i =>
    if i = Fin.last n then 1 else Polynomial.X ^ ((i : ℕ) + 1)
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ[X] :=
    A.updateRow (Fin.last n) (∑ i, c i • A i)
  have hc : c (Fin.last n) = 1 := by simp [c]
  have hdet : B.det = A.det := by
    dsimp [B]
    rw [Matrix.det_updateRow_sum, hc, one_smul]
  have htri : B.IsUpperTriangular := by
    intro i j hij
    by_cases hil : i = Fin.last n
    · subst i
      simp only [B, Matrix.updateRow_self]
      -- weighted row sum at the final row
      have hA : ∀ i k, A i k =
          (if i = k then 1 else 0) - if finRotate (n + 1) i = k then Polynomial.X else 0 := by
        intro i k
        simp [A, P, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
          Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply, finRotate_apply]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hsumA : (∑ i, c i * A i j) =
          ∑ i, c i * ((if i = j then 1 else 0) -
            if finRotate (n + 1) i = j then Polynomial.X else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hA]
      rw [hsumA]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      have hs1 : (∑ x, c x * if x = j then 1 else 0) = c j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro b hb hbj
          simp [hbj]
        · intro hj
          exact (hj (Finset.mem_univ _)).elim
      let k : Fin (n + 1) := (finRotate (n + 1)).symm j
      have hs2 : (∑ x, c x * if finRotate (n + 1) x = j then Polynomial.X else 0) =
          c k * Polynomial.X := by
        rw [Finset.sum_eq_single k]
        · rw [if_pos (by simp [k])]
        · intro b hb hbk
          have hrot : finRotate (n + 1) b ≠ j := by
            intro hrot
            apply hbk
            apply (finRotate (n + 1)).injective
            simpa [k] using hrot
          rw [if_neg hrot]
          simp
        · intro hk
          exact (hk (Finset.mem_univ _)).elim
      rw [hs1, hs2]
      have hcshift : c k * Polynomial.X = c j := by
        by_cases hj0 : j = 0
        · subst j
          have hjlast : (0 : Fin (n + 1)) ≠ Fin.last n :=
            Fin.ne_of_lt hij
          have hk0 : k = Fin.last n := by
            apply (finRotate (n + 1)).injective
            simp [k]
          simp [k, hk0, c, hjlast]
        · have hk_last : k ≠ Fin.last n := by
            intro hk
            apply hj0
            have := congrArg (finRotate (n + 1)) hk
            simpa [k] using this
          have hval : ((j - 1 : Fin (n + 1)) : ℕ) + 1 = j := by
            rw [Fin.val_sub_one_of_ne_zero hj0]
            exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
              (Fin.val_ne_zero_iff.mpr hj0))
          have hpred_last : (j - 1 : Fin (n + 1)) ≠ Fin.last n := by
            intro hpred
            have hlt : (j : ℕ) < n := Fin.val_lt_last (Fin.ne_of_lt hij)
            have hpredval := congrArg Fin.val hpred
            simp [Fin.val_sub_one_of_ne_zero hj0] at hpredval
            omega
          have hjlast : j ≠ Fin.last n := Fin.ne_of_lt hij
          simp [k, c, finRotate_symm_apply, hj0, hk_last,
            hjlast, hpred_last, hval]
          ring
      rw [hcshift]
      exact sub_self _
    · simp only [B, Matrix.updateRow_ne hil]
      -- non-final rows are already upper triangular
      have hne : i ≠ j := by
        intro h
        exact (lt_irrefl i) (h ▸ hij)
      have hnext : i + 1 ≠ j := by
        intro h
        have his : i < i + 1 := by
          rw [← finRotate_apply]
          exact (lt_finRotate_iff_ne_last i).2 hil
        have hij' : i < j := h ▸ his
        exact (not_lt_of_ge hij.le) hij'
      simp [A, P, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
        Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply,
        finRotate_apply, hne, hnext]
  rw [← hdet, Matrix.det_of_isUpperTriangular htri]
  have hlast : B (Fin.last n) (Fin.last n) = 1 - Polynomial.X ^ (n + 1) := by
    simp only [B, Matrix.updateRow_self, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hA : ∀ i k, A i k =
        (if i = k then 1 else 0) - if finRotate (n + 1) i = k then Polynomial.X else 0 := by
      intro i k
      simp [A, P, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
        Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply, finRotate_apply]
    have hsumA : (∑ i, c i * A i (Fin.last n)) =
        ∑ i, c i * ((if i = Fin.last n then 1 else 0) -
          if finRotate (n + 1) i = Fin.last n then Polynomial.X else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hA]
    rw [hsumA]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    have hs1 : (∑ x, c x * if x = Fin.last n then 1 else 0) = c (Fin.last n) := by
      rw [Finset.sum_eq_single (Fin.last n)]
      · simp
      · intro b hb hbj
        simp [hbj]
      · intro hj
        exact (hj (Finset.mem_univ _)).elim
    let k : Fin (n + 1) := (finRotate (n + 1)).symm (Fin.last n)
    have hs2 : (∑ x, c x * if finRotate (n + 1) x = Fin.last n then Polynomial.X else 0) =
        c k * Polynomial.X := by
      rw [Finset.sum_eq_single k]
      · rw [if_pos (by simp [k])]
      · intro b hb hbk
        have hrot : finRotate (n + 1) b ≠ Fin.last n := by
          intro hrot
          apply hbk
          apply (finRotate (n + 1)).injective
          simpa [k] using hrot
        rw [if_neg hrot]
        simp
      · intro hk
        exact (hk (Finset.mem_univ _)).elim
    rw [hs1, hs2, hc]
    by_cases hn : n = 0
    · subst n
      simp [k, c, finRotate_symm_apply]
    · have hkval : ((k : Fin (n + 1)) : ℕ) = n - 1 := by
        have hlast0 : (Fin.last n : Fin (n + 1)) ≠ 0 := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
          omega
        simp [k, finRotate_symm_apply, Fin.val_sub_one_of_ne_zero hlast0]
      have hk_last : k ≠ Fin.last n := by
        intro hk
        have := congrArg Fin.val hk
        have hlt : n - 1 < n := Nat.sub_lt (Nat.zero_lt_of_ne_zero hn) Nat.zero_lt_one
        rw [hkval] at this
        exact (Nat.ne_of_lt hlt) this
      have hkexp : (k : ℕ) + 1 = n := by
        rw [hkval]
        exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)
      simp [k, c, finRotate_symm_apply, hn, hk_last, hkval]
      have hlast0 : (Fin.last n : Fin (n + 1)) ≠ 0 := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
        omega
      have hpredval : ((Fin.last n - 1 : Fin (n + 1)) : ℕ) = n - 1 := by
        rw [Fin.val_sub_one_of_ne_zero hlast0]
        rfl
      have hpredexp : ((Fin.last n - 1 : Fin (n + 1)) : ℕ) + 1 = n := by
        rw [hpredval]
        exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)
      rw [hpredexp]
      rw [pow_succ]
  rw [Finset.prod_eq_single (Fin.last n)]
  · rw [hlast]
  · intro b hb hbl
    simp only [B, Matrix.updateRow_ne hbl]
    have hbn : b ≠ Fin.last n := hbl
    by_cases hn : n = 0
    · subst n
      have hb0 : b = 0 := Fin.eq_zero b
      exact (hbn (by simpa using hb0)).elim
    simp [A, P, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply, finRotate_apply,
      hbn, hn]
  · intro h
    exact (h (Finset.mem_univ _)).elim

def actualA {G : Type} [Group G] [Fintype G] (m n : ℕ) : Rep ℚ G :=
  if m = 1 ∧ n = 1 then Rep.of (Representation.leftRegular ℚ G)
  else Rep.of (Representation.trivial ℚ G PUnit)

def actualB {G : Type} [Group G] (r c m n : ℕ) : Rep ℚ G :=
  if m = r ∧ n = r then Rep.of (Representation.trivial ℚ G (Fin c → ℚ))
  else Rep.of (Representation.trivial ℚ G PUnit)

def actualHA {G : Type} [Group G] [Fintype G] [DecidableEq G] : Series G ℚ :=
  fun h d => if d = exponent 1 1 then
    Matrix.trace (LinearMap.toMatrix (MonoidAlgebra.basis G ℚ)
      (MonoidAlgebra.basis G ℚ) (Representation.leftRegular ℚ G h)) else 0

def actualHB {G : Type} [Group G] (r c : ℕ) : Series G ℚ :=
  fun h d => if d = exponent r r then
    Matrix.trace (LinearMap.toMatrix (Pi.basisFun ℚ (Fin c)) (Pi.basisFun ℚ (Fin c))
      (Representation.trivial ℚ G (Fin c → ℚ) h)) else 0

noncomputable def actualTraceA {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (m n : ℕ) (h : G) : ℚ :=
  if m = 1 ∧ n = 1 then (Representation.leftRegular ℚ G).character h
  else (Representation.trivial ℚ G PUnit).character h

noncomputable def actualTraceB {G : Type} [Group G]
    (r c m n : ℕ) (h : G) : ℚ :=
  if m = r ∧ n = r then (Representation.trivial ℚ G (Fin c → ℚ)).character h
  else (Representation.trivial ℚ G PUnit).character h

theorem actual_ledger_collision {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (g : G) (hr : 1 < orderOf g) :
    let r := orderOf g
    let c := Nat.card G / r
    ∃ D : MonsterPrimitiveMobiusRecovery.MonsterDenominator,
      0 < c ∧
      actualA (G := G) 1 1 = Rep.of (Representation.leftRegular ℚ G) ∧
      (∀ m n, m ≠ 1 ∨ n ≠ 1 →
        actualA (G := G) m n = Rep.of (Representation.trivial ℚ G PUnit)) ∧
      actualB (G := G) r c r r =
        Rep.of (Representation.trivial ℚ G (Fin c → ℚ)) ∧
      (∀ m n, m ≠ r ∨ n ≠ r →
        actualB (G := G) r c m n = Rep.of (Representation.trivial ℚ G PUnit)) ∧
      (∀ h : G, ∀ m n, actualHA (G := G) h (exponent m n) = actualTraceA (G := G) m n h ∧
        (m ≠ 1 ∨ n ≠ 1 → actualTraceA (G := G) m n h = 0)) ∧
      (∀ h : G, ∀ m n, actualHB (G := G) r c h (exponent m n) =
          actualTraceB (G := G) r c m n h ∧
        (m ≠ r ∨ n ≠ r → actualTraceB (G := G) r c m n h = 0)) ∧
      (∀ h : G, IsConj g h →
        Matrix.det (1 - (Polynomial.X : ℚ[X]) •
          (LinearMap.toMatrix (MonoidAlgebra.basis G ℚ) (MonoidAlgebra.basis G ℚ)
            (Representation.leftRegular ℚ G h)).map Polynomial.C) = (1 - Polynomial.X ^ r) ^ c ∧
        Matrix.det (1 - (Polynomial.X ^ r : ℚ[X]) •
          (LinearMap.toMatrix (Pi.basisFun ℚ (Fin c)) (Pi.basisFun ℚ (Fin c))
            (Representation.trivial ℚ G (Fin c → ℚ) h)).map Polynomial.C) = (1 - Polynomial.X ^ r) ^ c ∧
        actualHA (G := G) h (exponent 1 1) =
          Matrix.trace (LinearMap.toMatrix (MonoidAlgebra.basis G ℚ)
            (MonoidAlgebra.basis G ℚ) (Representation.leftRegular ℚ G h)) ∧
        actualHB (G := G) r c h (exponent r r) =
          Matrix.trace (LinearMap.toMatrix (Pi.basisFun ℚ (Fin c))
            (Pi.basisFun ℚ (Fin c))
            (Representation.trivial ℚ G (Fin c → ℚ) h)) ∧
        D.1 = PowerSeries.subst (MvPowerSeries.X 0 * MvPowerSeries.X 1)
          ((Matrix.det (1 - (Polynomial.X : ℚ[X]) •
            (LinearMap.toMatrix (MonoidAlgebra.basis G ℚ) (MonoidAlgebra.basis G ℚ)
              (Representation.leftRegular ℚ G h)).map Polynomial.C) : ℚ[X]) : PowerSeries ℚ) ∧
        D.1 = PowerSeries.subst (MvPowerSeries.X 0 * MvPowerSeries.X 1)
          ((Matrix.det (1 - (Polynomial.X ^ r : ℚ[X]) •
            (LinearMap.toMatrix (Pi.basisFun ℚ (Fin c)) (Pi.basisFun ℚ (Fin c))
              (Representation.trivial ℚ G (Fin c → ℚ) h)).map Polynomial.C) : ℚ[X]) : PowerSeries ℚ) ∧
        MonsterPrimitiveMobiusRecovery.negativeFormalLog D = logarithmicHistory (actualHA (G := G)) h ∧
        MonsterPrimitiveMobiusRecovery.negativeFormalLog D = logarithmicHistory (actualHB (G := G) r c) h ∧
        logarithmicHistory (actualHA (G := G)) h =
          logarithmicHistory (actualHB (G := G) r c) h ∧
        actualHA (G := G) h (exponent r r) = 0 ∧
        actualHB (G := G) r c h (exponent r r) = (c : ℚ)) := by
  let det_reindex_cycle
      {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
      (r : ℕ) (hr : 0 < r) (p : Equiv.Perm α) (E : α ≃ Fin r × ι)
      (hp : ∀ x, E (p x) = (finRotate r (E x).1, (E x).2)) :
      Matrix.det (1 - (Polynomial.X : ℚ[X]) • p.permMatrix ℚ[X]) =
        (1 - Polynomial.X ^ r) ^ Fintype.card ι := by
    have hP : Matrix.reindex E E (p.permMatrix ℚ[X]) =
        Matrix.blockDiagonal (fun _ : ι => (finRotate r).permMatrix ℚ[X]) := by
      apply Matrix.ext
      intro i j
      rcases i with ⟨i, qi⟩
      rcases j with ⟨j, qj⟩
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.blockDiagonal_apply]
      by_cases hq : qi = qj
      · subst qj
        have heq : p (E.symm (i, qi)) = E.symm (finRotate r i, qi) := by
          apply E.injective
          simpa using hp (E.symm (i, qi))
        simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, heq]
      · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hp, hq]
        by_contra hh
        have := congrArg E hh
        rw [hp] at this
        exact hq (by simpa using congrArg Prod.snd this)
    have hA : Matrix.reindex E E
        (1 - (Polynomial.X : ℚ[X]) • p.permMatrix ℚ[X]) =
        1 - (Polynomial.X : ℚ[X]) • Matrix.blockDiagonal
          (fun _ : ι => (finRotate r).permMatrix ℚ[X]) := by
      apply Matrix.ext
      intro i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply, Matrix.sub_apply,
        Matrix.smul_apply]
      have hpij := congrArg (fun M : Matrix (Fin r × ι) (Fin r × ι) ℚ[X] => M i j) hP
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply] at hpij
      rw [hpij]
      by_cases h : E.symm i = E.symm j
      · have hij : i = j := by simpa using congrArg E h
        simp [h, hij]
      · have hij : i ≠ j := by
          intro hij
          apply h
          simpa [hij]
        simp [h, hij]
    rw [← Matrix.det_reindex_self E]
    rw [hA]
    have hBD : 1 - (Polynomial.X : ℚ[X]) • Matrix.blockDiagonal
          (fun _ : ι => (finRotate r).permMatrix ℚ[X]) =
        Matrix.blockDiagonal (fun q : ι =>
          1 - (Polynomial.X : ℚ[X]) • (finRotate r).permMatrix ℚ[X]) := by
      apply Matrix.ext
      intro i j
      rcases i with ⟨i, qi⟩
      rcases j with ⟨j, qj⟩
      by_cases hq : qi = qj <;>
        simp [Matrix.blockDiagonal_apply, Matrix.one_apply, Matrix.sub_apply,
          Matrix.smul_apply, hq]
    rw [hBD]
    rw [Matrix.det_blockDiagonal]
    simp_rw [single_cycle_det r hr]
    rw [Finset.prod_const]
    simp

  let quotient_bot_period
      {G : Type} [Group G] [Fintype G] (h : G) (q : G ⧸ (⊥ : Subgroup G)) :
      MulAction.period h q = orderOf h := by
    apply Nat.dvd_antisymm
    · exact MulAction.period_dvd_orderOf h q
    · apply orderOf_dvd_of_pow_eq_one
      have hfix : h ^ MulAction.period h q • q = q :=
        MulAction.pow_period_smul h q
      have hmap := congrArg (fun x : G ⧸ (⊥ : Subgroup G) =>
        (QuotientGroup.quotientBot x : G)) hfix
      have hsmul : QuotientGroup.quotientBot (h ^ MulAction.period h q • q) =
          h ^ MulAction.period h q * QuotientGroup.quotientBot q := by
        refine Quotient.inductionOn' q (fun x => ?_)
        rfl
      have hm : (h ^ MulAction.period h q) *
          (QuotientGroup.quotientBot q : G) = QuotientGroup.quotientBot q := by
        simpa only [hsmul] using hmap
      exact mul_right_cancel (hm.trans (one_mul _).symm)

  let regularOrbitEquiv {G : Type} [Group G] [Fintype G] (h : G) :
      G ≃ Σ q : MulAction.orbitRel.Quotient (Subgroup.zpowers h) (G ⧸ (⊥ : Subgroup G)),
        ZMod (Function.minimalPeriod (fun x : G ⧸ (⊥ : Subgroup G) => h • x) (Quotient.out q)) :=
    (QuotientGroup.quotientBot.toEquiv.symm.trans
      (Subgroup.quotientEquivSigmaZMod (⊥ : Subgroup G) h))

  let regularOrbitEquiv_apply_smul
      {G : Type} [Group G] [Fintype G] (h : G)
      (q : MulAction.orbitRel.Quotient (Subgroup.zpowers h) (G ⧸ (⊥ : Subgroup G)))
      (j : ZMod (Function.minimalPeriod (fun x : G ⧸ (⊥ : Subgroup G) => h • x)
        (Quotient.out q))) :
      regularOrbitEquiv h (h *
          (regularOrbitEquiv h).symm ⟨q, j⟩) = ⟨q, j + 1⟩ := by
    let B : (G ⧸ (⊥ : Subgroup G)) ≃ G := QuotientGroup.quotientBot.toEquiv
    let E₀ := Subgroup.quotientEquivSigmaZMod (⊥ : Subgroup G) h
    have hB (y : G ⧸ (⊥ : Subgroup G)) : B.symm (h * B y) = h • y := by
      have hBmap : B (h • y) = h * B y := by
        refine Quotient.inductionOn' y (fun x => ?_)
        rfl
      apply B.injective
      rw [B.apply_symm_apply]
      exact hBmap.symm
    change E₀ (B.symm (h * B (E₀.symm ⟨q, j⟩))) = ⟨q, j + 1⟩
    rw [hB, Subgroup.quotientEquivSigmaZMod_symm_apply]
    change E₀ (h • (h ^ (j.cast : ℤ) • Quotient.out q)) = ⟨q, j + 1⟩
    have hz : h * h ^ (j.cast : ℤ) = h ^ ((1 : ℤ) + j.cast) := by
      let n : ℤ := j.cast
      calc
        h * h ^ n = h ^ (1 : ℤ) * h ^ n := by simp
        _ = h ^ ((1 : ℤ) + n) := by rw [← zpow_add h]
    have hact : (h * h ^ (j.cast : ℤ)) • Quotient.out q =
        h ^ ((1 : ℤ) + j.cast) • Quotient.out q := congrArg (fun a : G => a • Quotient.out q) hz
    rw [← mul_smul]
    change E₀ ((h * h ^ (j.cast : ℤ)) • Quotient.out q) = ⟨q, j + 1⟩
    rw [hact, Subgroup.quotientEquivSigmaZMod_apply]
    congr 1
    simp [ZMod.intCast_zmod_cast, add_comm]

  let regularOrbitEquiv_period
      {G : Type} [Group G] [Fintype G] (h : G) (q : MulAction.orbitRel.Quotient
        (Subgroup.zpowers h) (G ⧸ (⊥ : Subgroup G))) :
      Function.minimalPeriod (fun x : G ⧸ (⊥ : Subgroup G) => h • x) (Quotient.out q) = orderOf h := by
    change MulAction.period h (Quotient.out q) = orderOf h
    exact quotient_bot_period h (Quotient.out q)

  let zmod_cast_add {m n : ℕ} (h : m = n) (x : ZMod m) :
      Equiv.cast (congrArg ZMod h) (x + 1) =
        Equiv.cast (congrArg ZMod h) x + 1 := by
    cases h
    rfl

  let regular_perm_det
      {G : Type} [Group G] [Fintype G] [DecidableEq G]
      (h : G) (r : ℕ) (hr : 0 < r) (hrord : orderOf h = r) :
      Matrix.det (1 - (Polynomial.X : ℚ[X]) • (Equiv.mulLeft h⁻¹).permMatrix ℚ[X]) =
        (1 - Polynomial.X ^ r) ^ (Nat.card G / r) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    let a : G := h⁻¹
    have haord : orderOf a = n + 1 := by
      simp [a, hrord]
    have hapos : 0 < orderOf a := by simp [haord]
    let Q := MulAction.orbitRel.Quotient (Subgroup.zpowers a) (G ⧸ (⊥ : Subgroup G))
    letI : Fintype Q := Fintype.ofFinite Q
    letI : DecidableEq Q := Classical.decEq Q
    let E0 := regularOrbitEquiv a
    have hperiod (q : Q) :
        Function.minimalPeriod (fun x : G ⧸ (⊥ : Subgroup G) => a • x) (Quotient.out q) = n + 1 := by
      simpa [haord] using regularOrbitEquiv_period a q
    let E1 : (Σ q : Q, ZMod (Function.minimalPeriod
        (fun x : G ⧸ (⊥ : Subgroup G) => a • x) (Quotient.out q))) ≃
        (Σ _q : Q, ZMod (n + 1)) :=
      Equiv.sigmaCongrRight (fun q => Equiv.cast (congrArg ZMod (hperiod q)))
    let E2 := E0.trans E1
    let E3 := E2.trans (Equiv.sigmaEquivProd Q (ZMod (n + 1)))
    let E4 := E3.trans (Equiv.prodComm Q (ZMod (n + 1)))
    let E : G ≃ ZMod (n + 1) × Q := E4
    have hE : ∀ x : G, E ((Equiv.mulLeft a) x) =
        (finRotate (n + 1) (E x).1, (E x).2) := by
      intro x
      let q : Q := (E0 x).1
      let j : ZMod (Function.minimalPeriod (fun x : G ⧸ (⊥ : Subgroup G) => a • x)
        (Quotient.out q)) := (E0 x).2
      have hsmul := regularOrbitEquiv_apply_smul a q j
      have hsmul' : E0 (a * E0.symm ⟨q, j⟩) = ⟨q, j + 1⟩ := hsmul
      have hy : E0 x = ⟨q, j⟩ := by
        simp [q, j]
      have hx : x = E0.symm ⟨q, j⟩ := by
        simpa using congrArg E0.symm hy
      have ha : a * E0.symm ⟨q, j⟩ = E0.symm ⟨q, j + 1⟩ := by
        apply E0.injective
        exact hsmul'.trans (E0.apply_symm_apply _).symm
      rw [hx]
      change E (a * E0.symm ⟨q, j⟩) = _
      rw [ha]
      have hcoord (q : Q)
          (j : ZMod (Function.minimalPeriod (fun x : G ⧸ (⊥ : Subgroup G) => a • x)
            (Quotient.out q))) :
          E (E0.symm ⟨q, j⟩) = ((Equiv.cast (congrArg ZMod (hperiod q)) j), q) := by
        dsimp [E, E4, E3, E2, E1]
        simp
      rw [hcoord, hcoord]
      apply Prod.ext
      · have hcast (j : ZMod (Function.minimalPeriod
            (fun x : G ⧸ (⊥ : Subgroup G) => a • x) (Quotient.out q))) :
              Equiv.cast (congrArg ZMod (hperiod q)) (j + 1) =
              finRotate (n + 1) (Equiv.cast (congrArg ZMod (hperiod q)) j) := by
          rw [zmod_cast_add (hperiod q) j]
          exact (finRotate_apply _).symm
        exact hcast j
      · rfl
    have hdet := det_reindex_cycle (n + 1) (Nat.succ_pos n)
      (Equiv.mulLeft a) E hE
    have hcard : Nat.card G = (n + 1) * Fintype.card Q := by
      have hsum := Subgroup.index_eq_sum_minimalPeriod (⊥ : Subgroup G) a
      rw [Subgroup.index_bot] at hsum
      simpa [Q, hperiod, Nat.mul_comm] using hsum
    have hquot : Nat.card G / (n + 1) = Fintype.card Q :=
      Nat.div_eq_of_eq_mul_right (Nat.succ_pos n) hcard
    rw [hquot]
    simpa [a] using hdet

  let left_regular_matrix {G : Type} [Group G] [Fintype G] [DecidableEq G]
      (h : G) :
      LinearMap.toMatrix (MonoidAlgebra.basis G ℚ) (MonoidAlgebra.basis G ℚ)
        (Representation.leftRegular ℚ G h) =
        (Equiv.mulLeft h⁻¹).permMatrix ℚ := by
    apply Matrix.ext
    intro i j
    rw [LinearMap.toMatrix_apply]
    simp only [Representation.leftRegular, Representation.ofMulAction,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, MonoidAlgebra.basis,
      Finsupp.single_apply, map_one]
    by_cases hij : i = h * j
    · subst i
      simp
    · have hnot : h⁻¹ * i ≠ j := by
        intro hj
        apply hij
        calc
          i = h * (h⁻¹ * i) := by group
          _ = h * j := by rw [hj]
      simp [hij, hnot]

  let trivial_det {G : Type} [Group G] (h : G) (c r : ℕ) :
      Matrix.det (1 - (Polynomial.X ^ r : ℚ[X]) •
        (LinearMap.toMatrix (Pi.basisFun ℚ (Fin c)) (Pi.basisFun ℚ (Fin c))
          (Representation.trivial ℚ G (Fin c → ℚ) h)).map Polynomial.C) =
        (1 - Polynomial.X ^ r) ^ c := by
    have hmat : LinearMap.toMatrix (Pi.basisFun ℚ (Fin c)) (Pi.basisFun ℚ (Fin c))
        (Representation.trivial ℚ G (Fin c → ℚ) h) = 1 := by
      simp [Representation.trivial]
    rw [hmat]
    rw [Matrix.map_one (Polynomial.C : ℚ → ℚ[X]) (by simp) (by simp)]
    have hdiag : (1 - (Polynomial.X ^ r : ℚ[X]) • (1 : Matrix (Fin c) (Fin c) ℚ[X])) =
        Matrix.diagonal (fun _ => 1 - Polynomial.X ^ r) := by
      ext i j
      by_cases hij : i = j <;>
        simp [Matrix.one_apply, Matrix.diagonal_apply, Matrix.smul_apply,
          Matrix.sub_apply, hij]
    rw [hdiag, Matrix.det_diagonal]
    simp

  let regular_action_det {G : Type} [Group G] [Fintype G] [DecidableEq G]
      (h : G) (r : ℕ) (hr : 0 < r) (hrord : orderOf h = r) :
      Matrix.det (1 - (Polynomial.X : ℚ[X]) •
        (LinearMap.toMatrix (MonoidAlgebra.basis G ℚ) (MonoidAlgebra.basis G ℚ)
          (Representation.leftRegular ℚ G h)).map Polynomial.C) =
        (1 - Polynomial.X ^ r) ^ (Nat.card G / r) := by
    rw [left_regular_matrix h]
    have hmap : ((Equiv.mulLeft h⁻¹).permMatrix ℚ).map (Polynomial.C : ℚ → ℚ[X]) =
        (Equiv.mulLeft h⁻¹).permMatrix ℚ[X] := by
      ext i j
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    rw [hmap]
    exact regular_perm_det h r hr hrord

  let left_regular_trace {G : Type} [Group G] [Fintype G] [DecidableEq G]
      (h : G) :
      Matrix.trace (LinearMap.toMatrix (MonoidAlgebra.basis G ℚ) (MonoidAlgebra.basis G ℚ)
        (Representation.leftRegular ℚ G h)) =
        if h = 1 then (Fintype.card G : ℚ) else 0 := by
    rw [left_regular_matrix h]
    simp only [Matrix.trace, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    by_cases hh : h = 1
    · subst h
      simp
    · have hdiag : ∀ i : G, h⁻¹ * i ≠ i := by
        intro i hi
        apply hh
        apply mul_right_cancel (b := i)
        calc
          h * i = i := by
            have hmul := congrArg (fun x => h * x) hi
            simpa using hmul.symm
          _ = 1 * i := by simp
      simp [hh, hdiag]

  let left_regular_trace_pow {G : Type} [Group G] [Fintype G] [DecidableEq G]
      (h : G) (r k : ℕ) (hrord : orderOf h = r) :
      Matrix.trace (LinearMap.toMatrix (MonoidAlgebra.basis G ℚ) (MonoidAlgebra.basis G ℚ)
        (Representation.leftRegular ℚ G (h ^ k))) =
        if r ∣ k then (Fintype.card G : ℚ) else 0 := by
    rw [left_regular_trace]
    by_cases hdiv : r ∣ k
    · have hp : h ^ k = 1 := by
        apply (orderOf_dvd_iff_pow_eq_one).1
        simpa [hrord] using hdiv
      simp [hp, hdiv]
    · have hp : h ^ k ≠ 1 := by
        intro hp
        apply hdiv
        simpa [hrord] using (orderOf_dvd_iff_pow_eq_one).2 hp
      simp [hp, hdiv]

  let log_derivative_mul :
      derivative ℚ (log ℚ) * (1 + X) = 1 := by
    have h := congrArg (rescale (-1 : ℚ)) (mk_one_mul_one_sub_eq_one ℚ)
    have he : rescale (-1 : ℚ) (mk 1) = derivative ℚ (log ℚ) := by
      ext n
      simp [deriv_log]
    simpa [he] using h

  let logOf_derivative_mul (f : PowerSeries ℚ)
      (hf : constantCoeff f = 1) :
      derivative ℚ (logOf f) * f = derivative ℚ f := by
    have hs : HasSubst (f - 1) := .of_constantCoeff_zero (by
      change constantCoeff (f - 1) = 0
      simp [hf])
    have hone : subst (f - 1) (1 : PowerSeries ℚ) = 1 := by
      rw [← coe_substAlgHom hs]
      exact map_one _
    have h := congrArg (subst (f - 1)) log_derivative_mul
    have hmul : (derivative ℚ (log ℚ)).subst (f - 1) * f = 1 := by
      simpa only [subst_mul hs, subst_add hs, hone, subst_X hs,
        add_sub_cancel] using h
    rw [logOf_eq, derivative_subst hs]
    have hder : derivative ℚ (f - 1) = derivative ℚ f := by simp
    rw [hder]
    calc
      (derivative ℚ (log ℚ)).subst (f - 1) * derivative ℚ f * f =
          ((derivative ℚ (log ℚ)).subst (f - 1) * f) * derivative ℚ f := by ring
      _ = derivative ℚ f := by rw [hmul, one_mul]

  let logOf_mul (f g : PowerSeries ℚ)
      (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
      logOf (f * g) = logOf f + logOf g := by
    have hfg : constantCoeff (f * g) = 1 := by simp [hf, hg]
    apply derivative.ext
    · have h1 := logOf_derivative_mul (f * g) hfg
      have h2 := logOf_derivative_mul f hf
      have h3 := logOf_derivative_mul g hg
      apply mul_right_cancel₀ (show f * g ≠ 0 by
        intro hz
        have := congrArg constantCoeff hz
        simp [hf, hg] at this)
      rw [map_add]
      calc
        derivative ℚ (logOf (f * g)) * (f * g) = derivative ℚ (f * g) := h1
        _ = derivative ℚ f * g + f * derivative ℚ g := by rw [Derivation.leibniz]; ring
        _ = (derivative ℚ (logOf f) + derivative ℚ (logOf g)) * (f * g) := by
          rw [← h2, ← h3]
          ring
    · simp [constantCoeff_logOf, hf, hg, hfg]

  let logOf_pow (f : PowerSeries ℚ)
      (hf : constantCoeff f = 1) (c : ℕ) :
      logOf (f ^ c) = c * logOf f := by
    induction c with
    | zero =>
        have hOne : logOf (1 : PowerSeries ℚ) = 0 := by
          rw [logOf_eq]
          simp
        simp [hOne]
    | succ c ih =>
        rw [pow_succ, logOf_mul _ _ (by simp [hf]) hf, ih]
        push_cast
        ring

  let factor_log_coeff (r c n : ℕ) (hr : 0 < r) :
      coeff n (-logOf ((1 - X ^ r : PowerSeries ℚ) ^ c)) =
        if r ∣ n ∧ n ≠ 0 then (c : ℚ) / ((n / r : ℕ) : ℚ) else 0 := by
    have hf : constantCoeff (1 - X ^ r : PowerSeries ℚ) = 1 := by
      simp [← coeff_zero_eq_constantCoeff, coeff_X_pow, Ne.symm hr.ne']
    have hlog : logOf (1 - X ^ r : PowerSeries ℚ) =
        subst (X ^ r) (rescale (-1 : ℚ) (log ℚ)) := by
      rw [logOf_eq, show (1 - X ^ r : PowerSeries ℚ) - 1 = -(X ^ r) by ring]
      rw [rescale_eq_subst,
        subst_comp_subst_apply (HasSubst.smul_X' (-1)) (HasSubst.X_pow hr.ne')]
      have hs : HasSubst (X ^ r : PowerSeries ℚ) := .X_pow hr.ne'
      rw [subst_smul hs, subst_X hs]
      simp
    have hcoeff (n : ℕ) : coeff n (logOf (1 - X ^ r : PowerSeries ℚ)) =
        if r ∣ n then -(1 / ((n / r : ℕ) : ℚ)) else 0 := by
      rw [hlog, coeff_subst_X_pow hr.ne']
      by_cases hd : r ∣ n
      · rw [if_pos hd, if_pos hd, coeff_rescale, coeff_log]
        by_cases hq : n / r = 0
        · have hn : n = 0 := by
            have hm := Nat.mul_div_cancel' hd
            simpa [hq] using hm.symm
          simp [hn]
        · rw [if_neg hq]
          simp only [Algebra.algebraMap_self, RingHom.id_apply]
          have hp : (-1 : ℚ) ^ (n / r) * (-1 : ℚ) ^ (n / r) = 1 := by
            rw [← pow_add, ← two_mul, pow_mul]
            norm_num
          rw [pow_succ]
          calc
            (-1 : ℚ) ^ (n / r) *
                ((-1 : ℚ) ^ (n / r) * -1 / ((n / r : ℕ) : ℚ)) =
                ((-1 : ℚ) ^ (n / r) * (-1 : ℚ) ^ (n / r)) *
                  (-1 / ((n / r : ℕ) : ℚ)) := by ring
            _ = -(1 / ((n / r : ℕ) : ℚ)) := by rw [hp]; ring
      · simp [hd]
    rw [logOf_pow _ hf]
    rw [map_neg, show (↑c : PowerSeries ℚ) = C (c : ℚ) by simp, coeff_C_mul]
    rw [hcoeff]
    by_cases hd : r ∣ n
    · rw [if_pos hd]
      by_cases hn : n = 0
      · simp [hn]
      · rw [if_pos ⟨hd, hn⟩]
        ring
    · simp [hd]

  let z : MvPowerSeries (Fin 2) ℚ :=
    MvPowerSeries.monomial (exponent 1 1) 1

  let z_eq_pq : z = MvPowerSeries.X 0 * MvPowerSeries.X 1 := by
    have he : exponent 1 1 = Finsupp.single 0 1 + Finsupp.single 1 1 := by
      ext i
      fin_cases i <;> simp [exponent]
    change MvPowerSeries.monomial (exponent 1 1) (1 : ℚ) =
      MvPowerSeries.X 0 * MvPowerSeries.X 1
    rw [MvPowerSeries.X, MvPowerSeries.X,
      MvPowerSeries.monomial_mul_monomial]
    rw [he]
    simp

  let z_pow (k : ℕ) :
      z ^ k = MvPowerSeries.monomial (exponent k k) (1 : ℚ) := by
    have he : k • exponent 1 1 = exponent k k := by
      ext i
      fin_cases i <;> simp [exponent]
    simp [z, MvPowerSeries.monomial_pow, he]

  let z_constantCoeff : MvPowerSeries.constantCoeff z = 0 := by
    have he : (0 : Fin 2 →₀ ℕ) ≠ exponent 1 1 := by
      intro h
      have hh := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
      simp [exponent] at hh
    simp [z, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_monomial, he]

  let z_hasSubst : PowerSeries.HasSubst z :=
    .of_constantCoeff_zero z_constantCoeff

  let coeff_subst_z (f : PowerSeries ℚ) (d : Fin 2 →₀ ℕ) :
      MvPowerSeries.coeff d (PowerSeries.subst z f) =
        if d 0 = d 1 then PowerSeries.coeff (d 0) f else 0 := by
    rw [PowerSeries.coeff_subst z_hasSubst]
    by_cases hd : d 0 = d 1
    · rw [if_pos hd, finsum_eq_single _ (d 0)]
      · rw [z_pow, MvPowerSeries.coeff_monomial]
        have hde : d = exponent (d 0) (d 0) := by
          apply (finTwoArrowEquiv' ℕ).injective
          simp [exponent, hd]
        rw [if_pos hde]
        simp
      · intro k hk
        rw [z_pow, MvPowerSeries.coeff_monomial]
        by_cases he : d = exponent k k
        · exfalso
          apply hk
          have := congrArg (fun x : Fin 2 →₀ ℕ => x 0) he
          simpa [exponent] using this.symm
        · simp [he]
    · rw [if_neg hd]
      apply finsum_eq_zero_of_forall_eq_zero
      intro k
      rw [z_pow, MvPowerSeries.coeff_monomial]
      have he : d ≠ exponent k k := by
        intro he
        apply hd
        have h0 := congrArg (fun x : Fin 2 →₀ ℕ => x 0) he
        have h1 := congrArg (fun x : Fin 2 →₀ ℕ => x 1) he
        simpa [exponent] using h0.trans h1.symm
      simp [he]

  let oneVarFactor (r c : ℕ) : PowerSeries ℚ := (1 - X ^ r) ^ c

  let factor_constantCoeff (r c : ℕ) (hr : 0 < r) :
      constantCoeff (oneVarFactor r c) = 1 := by
    have h : constantCoeff (1 - X ^ r : PowerSeries ℚ) = 1 := by
      simp [← coeff_zero_eq_constantCoeff, coeff_X_pow, Ne.symm hr.ne']
    simp [oneVarFactor, h]

  let factorDenominator (r c : ℕ) (hr : 0 < r) : MonsterPrimitiveMobiusRecovery.MonsterDenominator :=
    ⟨PowerSeries.subst z (oneVarFactor r c), by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst_z]
      simpa [← coeff_zero_eq_constantCoeff] using factor_constantCoeff r c hr⟩

  let factor_negativeFormalLog (r c : ℕ) (hr : 0 < r) :
      MonsterPrimitiveMobiusRecovery.negativeFormalLog (factorDenominator r c hr) =
        PowerSeries.subst z (-logOf (oneVarFactor r c)) := by
    have hf : constantCoeff (oneVarFactor r c) = 1 := factor_constantCoeff r c hr
    have hs : HasSubst (oneVarFactor r c - 1) := .of_constantCoeff_zero (by
      change constantCoeff (oneVarFactor r c - 1) = 0
      simp [hf])
    rw [MonsterPrimitiveMobiusRecovery.negativeFormalLog, MvPowerSeries.substAlgHom_apply]
    change -PowerSeries.subst ((factorDenominator r c hr).1 - 1) (log ℚ) =
      PowerSeries.subst z (-logOf (oneVarFactor r c))
    rw [logOf_eq]
    rw [← coe_substAlgHom (R := ℚ) z_hasSubst, map_neg, coe_substAlgHom]
    rw [PowerSeries.subst_comp_subst_apply hs z_hasSubst]
    have hsub : PowerSeries.subst z (oneVarFactor r c - 1) =
        (factorDenominator r c hr).1 - 1 := by
      rw [PowerSeries.subst_sub z_hasSubst]
      have hone : PowerSeries.subst z (1 : PowerSeries ℚ) = 1 := by
        rw [← coe_substAlgHom (R := ℚ) z_hasSubst]
        exact map_one _
      simp [factorDenominator, hone]
    rw [hsub]

  let singletonA (t : G → ℚ) : Series G ℚ :=
    fun h d => if d = exponent 1 1 then t h else 0

  let singletonB (r : ℕ) (t : G → ℚ) : Series G ℚ :=
    fun h d => if d = exponent r r then t h else 0

  let singleton_history_eq
      (t : G → ℚ) (h : G) (r N c : ℕ) (hr : 0 < r) (hNc : N = r * c)
      (htrace : ∀ k : ℕ, t (h ^ k) = if r ∣ k then (N : ℚ) else 0) :
      logarithmicHistory (singletonA t) h =
        logarithmicHistory (singletonB r (fun _ => c)) h := by
    classical
    apply MvPowerSeries.ext
    intro d
    by_cases hd : d 0 = 0 ∨ d 1 = 0
    · have hnot : ¬(0 < d 0 ∧ 0 < d 1) := by omega
      simp [MvPowerSeries.coeff_apply, logarithmicHistory, singletonA, singletonB, hd, hnot]
    · have hpos : 0 < d 0 ∧ 0 < d 1 := by omega
      simp only [MvPowerSeries.coeff_apply, logarithmicHistory]
      rw [if_pos hpos, if_pos hpos]
      simp only [singletonA, singletonB]
      have hexp1 (a b : ℕ) : exponent a b = exponent 1 1 ↔ a = 1 ∧ b = 1 := by
        simp [exponent]
      have hexpr (a b : ℕ) : exponent a b = exponent r r ↔ a = r ∧ b = r := by
        simp [exponent]
      by_cases hdiag : d 0 = d 1
      · let n := d 0
        have hdeq : d = exponent n n := by
          apply (finTwoArrowEquiv' ℕ).injective
          simp [exponent, n, hdiag]
        rw [hdeq]
        simp [exponent]
        have hn : 0 < n := by simpa [n] using hpos.1
        have hA : (∑ x ∈ n.divisors,
            (if n / x = 1 then t (h ^ x) else 0) / (x : ℚ)) = t (h ^ n) / (n : ℚ) := by
          rw [Finset.sum_eq_single n]
          · have hnn : n / n = 1 := Nat.div_self hn
            simp [hnn]
          · intro b hb hbn
            have hbdiv : b ∣ n := Nat.dvd_of_mem_divisors hb
            have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hbdiv hn
            have hbne : n / b ≠ 1 := by
              intro hq
              have heq := (Nat.div_eq_iff_eq_mul_left hbpos hbdiv).mp hq
              exact hbn (by omega)
            simp [hbne]
          · intro hnm
            exact (hnm (Nat.mem_divisors.mpr ⟨dvd_refl n, hn.ne'⟩)).elim
        by_cases hdiv : r ∣ n
        · let q := n / r
          have hqpos : 0 < q := by
            exact Nat.div_pos (Nat.le_of_dvd (by omega) hdiv) hr
          have hqdiv : q ∣ n := by
            exact (Nat.div_dvd_iff_dvd_mul hdiv hr).2 (dvd_mul_left n r)
          have hqr : n / q = r := by
            apply (Nat.div_eq_iff_eq_mul_left hqpos hqdiv).2
            simpa [q, Nat.mul_comm] using (Nat.div_mul_cancel hdiv).symm
          have hB : (∑ x ∈ n.divisors,
              (if n / x = r then (c : ℚ) else 0) / (x : ℚ)) = c / (q : ℚ) := by
            rw [Finset.sum_eq_single q]
            · simp [hqr]
            · intro b hb hbq
              have hbdiv : b ∣ n := Nat.dvd_of_mem_divisors hb
              have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hbdiv hn
              have hbne : n / b ≠ r := by
                intro hbr
                have heq := (Nat.div_eq_iff_eq_mul_left hbpos hbdiv).mp hbr
                have hnq : n = r * q := by
                  simpa [q, Nat.mul_comm] using (Nat.div_mul_cancel hdiv).symm
                exact hbq (Nat.eq_of_mul_eq_mul_left hr (by omega))
              simp [hbne]
            · intro hqm
              exact (hqm (Nat.mem_divisors.mpr ⟨hqdiv, hn.ne'⟩)).elim
          rw [hA, hB, htrace n]
          rw [if_pos hdiv, hNc]
          field_simp [hn.ne', hqpos.ne']
          have hnr : (n : ℚ) = (q : ℚ) * r := by
            have hnrNat : n = q * r := by
              simpa [q] using (Nat.div_mul_cancel hdiv).symm
            exact_mod_cast hnrNat
          rw [hnr]
          push_cast
          ring
        · rw [hA]
          have hBzero : (∑ x ∈ n.divisors,
              (if n / x = r then (c : ℚ) else 0) / (x : ℚ)) = 0 := by
            apply Finset.sum_eq_zero
            intro b hb
            have hbdiv : b ∣ n := Nat.dvd_of_mem_divisors hb
            have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hbdiv hn
            have hbne : n / b ≠ r := by
              intro hbr
              apply hdiv
              have heq := (Nat.div_eq_iff_eq_mul_left hbpos hbdiv).mp hbr
              exact ⟨b, by omega⟩
            simp [hbne]
          rw [hBzero, htrace n]
          simp [hdiv]
      · apply Finset.sum_congr rfl
        intro k hk
        have hk0 : 0 < k := by
          have hkn : k ∣ Nat.gcd (d 0) (d 1) := Nat.dvd_of_mem_divisors hk
          exact Nat.pos_of_dvd_of_pos hkn
            (Nat.gcd_pos_of_pos_left _ hpos.1)
        have hk0d : k ∣ d 0 := dvd_trans (Nat.dvd_of_mem_divisors hk)
          (Nat.gcd_dvd_left _ _)
        have hk1d : k ∣ d 1 := dvd_trans (Nat.dvd_of_mem_divisors hk)
          (Nat.gcd_dvd_right _ _)
        by_cases he1 : exponent (d 0 / k) (d 1 / k) = exponent 1 1
        · have he := (hexp1 _ _).mp he1
          have h0 := (Nat.div_eq_iff_eq_mul_left hk0 hk0d).mp he.1
          have h1 := (Nat.div_eq_iff_eq_mul_left hk0 hk1d).mp he.2
          exact (hdiag (by omega)).elim
        · by_cases heR : exponent (d 0 / k) (d 1 / k) = exponent r r
          · have he := (hexpr _ _).mp heR
            have h0 := (Nat.div_eq_iff_eq_mul_left hk0 hk0d).mp he.1
            have h1 := (Nat.div_eq_iff_eq_mul_left hk0 hk1d).mp he.2
            exact (hdiag (by omega)).elim
          · simp [he1, heR]

  let singletonB_history_coeff (r c : ℕ) (hr : 0 < r) (h : G)
      (d : Fin 2 →₀ ℕ) :
      logarithmicHistory (singletonB r (fun _ => c)) h d =
        if d 0 = d 1 ∧ r ∣ d 0 ∧ d 0 ≠ 0 then
          (c : ℚ) / (((d 0) / r : ℕ) : ℚ) else 0 := by
    classical
    by_cases hpos : 0 < d 0 ∧ 0 < d 1
    · by_cases hdiag : d 0 = d 1
      · let n := d 0
        have hdeq : d = exponent n n := by
          apply (finTwoArrowEquiv' ℕ).injective
          simp [exponent, n, hdiag]
        rw [hdeq]
        have hn : 0 < n := by simpa [n] using hpos.1
        by_cases hdiv : r ∣ n
        · let q := n / r
          have hqpos : 0 < q := Nat.div_pos (Nat.le_of_dvd hn hdiv) hr
          have hqdiv : q ∣ n :=
            (Nat.div_dvd_iff_dvd_mul hdiv hr).2 (dvd_mul_left n r)
          have hqr : n / q = r := by
            apply (Nat.div_eq_iff_eq_mul_left hqpos hqdiv).2
            simpa [q, Nat.mul_comm] using (Nat.div_mul_cancel hdiv).symm
          have hB : (∑ x ∈ n.divisors,
              (if n / x = r then (c : ℚ) else 0) / (x : ℚ)) =
              (c : ℚ) / (q : ℚ) := by
            rw [Finset.sum_eq_single q]
            · simp [hqr]
            · intro b hb hbq
              have hbdiv : b ∣ n := Nat.dvd_of_mem_divisors hb
              have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hbdiv hn
              have hbne : n / b ≠ r := by
                intro hbr
                have heq := (Nat.div_eq_iff_eq_mul_left hbpos hbdiv).mp hbr
                have hnq : n = r * q := by
                  simpa [q, Nat.mul_comm] using (Nat.div_mul_cancel hdiv).symm
                exact hbq (Nat.eq_of_mul_eq_mul_left hr (by omega))
              simp [hbne]
            · intro hqm
              exact (hqm (Nat.mem_divisors.mpr ⟨hqdiv, hn.ne'⟩)).elim
          have hsum : logarithmicHistory (singletonB r (fun _ : G => c)) h
              (exponent n n) =
              ∑ x ∈ n.divisors,
                (if n / x = r then (c : ℚ) else 0) / (x : ℚ) := by
            simp [logarithmicHistory, singletonB, exponent, hn]
          rw [hsum, hB]
          simp [exponent, hdiv, hn.ne', q]
        · have hBzero : (∑ x ∈ n.divisors,
              (if n / x = r then (c : ℚ) else 0) / (x : ℚ)) = 0 := by
            apply Finset.sum_eq_zero
            intro b hb
            have hbdiv : b ∣ n := Nat.dvd_of_mem_divisors hb
            have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hbdiv hn
            have hbne : n / b ≠ r := by
              intro hbr
              apply hdiv
              have heq := (Nat.div_eq_iff_eq_mul_left hbpos hbdiv).mp hbr
              exact ⟨b, by omega⟩
            simp [hbne]
          have hsum : logarithmicHistory (singletonB r (fun _ : G => c)) h
              (exponent n n) =
              ∑ x ∈ n.divisors,
                (if n / x = r then (c : ℚ) else 0) / (x : ℚ) := by
            simp [logarithmicHistory, singletonB, exponent, hn]
          rw [hsum, hBzero]
          simp [exponent, hdiv]
      · have hzero : logarithmicHistory (singletonB r (fun _ : G => c)) h d = 0 := by
          simp only [logarithmicHistory, if_pos hpos]
          apply Finset.sum_eq_zero
          intro k hk
          have hk0 : 0 < k := by
            have hkn : k ∣ Nat.gcd (d 0) (d 1) := Nat.dvd_of_mem_divisors hk
            exact Nat.pos_of_dvd_of_pos hkn (Nat.gcd_pos_of_pos_left _ hpos.1)
          have hk0d : k ∣ d 0 := dvd_trans (Nat.dvd_of_mem_divisors hk) (Nat.gcd_dvd_left _ _)
          have hk1d : k ∣ d 1 := dvd_trans (Nat.dvd_of_mem_divisors hk) (Nat.gcd_dvd_right _ _)
          have he : exponent (d 0 / k) (d 1 / k) ≠ exponent r r := by
            intro he
            have h0 : d 0 / k = r := by simpa [exponent] using congrArg (fun e : Fin 2 →₀ ℕ => e 0) he
            have h1 : d 1 / k = r := by simpa [exponent] using congrArg (fun e : Fin 2 →₀ ℕ => e 1) he
            have h0' := (Nat.div_eq_iff_eq_mul_left hk0 hk0d).mp h0
            have h1' := (Nat.div_eq_iff_eq_mul_left hk0 hk1d).mp h1
            exact hdiag (by omega)
          simp [singletonB, he]
        rw [hzero]
        simp [hdiag]
    · have hnot : d 0 = 0 ∨ d 1 = 0 := by omega
      rcases hnot with h0 | h1
      · simp [logarithmicHistory, hpos, h0]
      · by_cases h0 : d 0 = 0
        · simp [logarithmicHistory, hpos, h0]
        · have hfalse : ¬(d 0 = d 1 ∧ r ∣ d 0 ∧ d 0 ≠ 0) := by
            intro hh
            exact h0 (by simpa [h1] using hh.1)
          rw [if_neg hfalse]
          simp [logarithmicHistory, hpos, h1]

  let factor_class_history
      (r c : ℕ) (hr : 0 < r) (h : G) (d : Fin 2 →₀ ℕ) :
      MvPowerSeries.coeff d (MonsterPrimitiveMobiusRecovery.negativeFormalLog (factorDenominator r c hr)) =
        logarithmicHistory (singletonB r (fun _ => c)) h d := by
    rw [factor_negativeFormalLog r c hr, coeff_subst_z,
      singletonB_history_coeff r c hr h d]
    change (if d 0 = d 1 then
        coeff (d 0) (-logOf ((1 - X ^ r : PowerSeries ℚ) ^ c)) else 0) = _
    rw [factor_log_coeff r c (d 0) hr]
    by_cases hdiag : d 0 = d 1
    · simp [hdiag]
    · simp [hdiag]

  let r := orderOf g
  let c := Nat.card G / r
  have hr0 : 0 < r := lt_trans (by omega : 0 < 1) hr
  have hdiv : r ∣ Nat.card G := by
    simpa [r, Nat.card_eq_fintype_card] using (orderOf_dvd_card (x := g))
  have hc : 0 < c := Nat.div_pos (Nat.le_of_dvd Nat.card_pos hdiv) hr0
  have hN : Nat.card G = r * c := by
    simpa [c, Nat.mul_comm] using (Nat.mul_div_cancel' hdiv).symm
  have hBridgeA : ∀ h : G, ∀ m n, actualHA (G := G) h (exponent m n) =
      actualTraceA (G := G) m n h ∧
      (m ≠ 1 ∨ n ≠ 1 → actualTraceA (G := G) m n h = 0) := by
    intro h m n
    have hzero : (Representation.trivial ℚ G PUnit).character h = 0 := by
      simp [Representation.character, Representation.trivial, LinearMap.trace_one,
        Module.finrank_eq_zero_of_subsingleton]
    by_cases hmn : m = 1 ∧ n = 1
    · rcases hmn with ⟨rfl, rfl⟩
      constructor
      · simpa [actualHA, actualTraceA, Representation.character] using
          (LinearMap.trace_eq_matrix_trace ℚ (MonoidAlgebra.basis G ℚ)
            (Representation.leftRegular ℚ G h)).symm
      · intro hbad
        rcases hbad with hb | hb <;> exact (hb rfl).elim
    · have hbad : m ≠ 1 ∨ n ≠ 1 := not_and_or.mp hmn
      constructor
      · simp [actualHA, exponent, hmn, actualTraceA, hzero]
      · intro _
        simp [actualTraceA, hmn, hzero]
  have hBridgeB : ∀ h : G, ∀ m n, actualHB (G := G) r c h (exponent m n) =
      actualTraceB (G := G) r c m n h ∧
      (m ≠ r ∨ n ≠ r → actualTraceB (G := G) r c m n h = 0) := by
    intro h m n
    have hzero : (Representation.trivial ℚ G PUnit).character h = 0 := by
      simp [Representation.character, Representation.trivial, LinearMap.trace_one,
        Module.finrank_eq_zero_of_subsingleton]
    by_cases hmn : m = r ∧ n = r
    · rcases hmn with ⟨rfl, rfl⟩
      constructor
      · simpa [actualHB, actualTraceB, Representation.character] using
          (LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ (Fin c))
            (Representation.trivial ℚ G (Fin c → ℚ) h)).symm
      · intro hbad
        rcases hbad with hb | hb <;> exact (hb rfl).elim
    · have hbad : m ≠ r ∨ n ≠ r := not_and_or.mp hmn
      constructor
      · simp [actualHB, exponent, hmn, actualTraceB, hzero]
      · intro _
        simp [actualTraceB, hmn, hzero]
  refine ⟨factorDenominator r c hr0, hc, ?_, ?_, ?_, ?_, hBridgeA, hBridgeB, ?_⟩
  · simp [actualA]
  · intro m n hmn
    rcases hmn with hm | hn
    · simp [actualA, hm]
    · simp [actualA, hn]
  · simp [actualB]
  · intro m n hmn
    rcases hmn with hm | hn
    · simp [actualB, hm]
    · simp [actualB, hn]
  · intro h hconj
    have hrh : orderOf h = r := by
      rcases hconj with ⟨u, hu⟩
      simpa [r] using (SemiconjBy.orderOf_eq (u : G) hu).symm
    have hdetA := regular_action_det h r hr0 hrh
    have hdetB := trivial_det h c r
    have htrace : ∀ k : ℕ,
        Matrix.trace (LinearMap.toMatrix (MonoidAlgebra.basis G ℚ)
          (MonoidAlgebra.basis G ℚ) (Representation.leftRegular ℚ G (h ^ k))) =
          if r ∣ k then (Nat.card G : ℚ) else 0 := by
      intro k
      simpa [Nat.card_eq_fintype_card] using left_regular_trace_pow h r k hrh
    have hb_series : actualHB (G := G) r c = singletonB r (fun _ : G => c) := by
      funext x d
      simp [actualHB, singletonB, Representation.trivial, Matrix.trace_one]
    have hHist : logarithmicHistory (actualHA (G := G)) h =
        logarithmicHistory (actualHB (G := G) r c) h := by
      rw [hb_series]
      change logarithmicHistory (singletonA (fun x : G =>
        Matrix.trace (LinearMap.toMatrix (MonoidAlgebra.basis G ℚ)
          (MonoidAlgebra.basis G ℚ) (Representation.leftRegular ℚ G x)))) h =
          logarithmicHistory (singletonB r (fun _ : G => c)) h
      exact singleton_history_eq _ h r (Nat.card G) c hr0 hN htrace
    have hLogB : MonsterPrimitiveMobiusRecovery.negativeFormalLog (factorDenominator r c hr0) =
        logarithmicHistory (actualHB (G := G) r c) h := by
      rw [hb_series]
      apply MvPowerSeries.ext
      intro d
      change MvPowerSeries.coeff d (MonsterPrimitiveMobiusRecovery.negativeFormalLog (factorDenominator r c hr0)) =
        logarithmicHistory (singletonB r (fun _ : G => c)) h d
      exact factor_class_history r c hr0 h d
    have hLogA : MonsterPrimitiveMobiusRecovery.negativeFormalLog (factorDenominator r c hr0) =
        logarithmicHistory (actualHA (G := G)) h := hLogB.trans hHist.symm
    have hD1 : (factorDenominator r c hr0).1 = PowerSeries.subst z
        ((Matrix.det (1 - (Polynomial.X : ℚ[X]) •
          (LinearMap.toMatrix (MonoidAlgebra.basis G ℚ) (MonoidAlgebra.basis G ℚ)
            (Representation.leftRegular ℚ G h)).map Polynomial.C) : ℚ[X]) : PowerSeries ℚ) := by
      rw [hdetA]
      simp [factorDenominator, oneVarFactor, c, Nat.card_eq_fintype_card]
    have hD2 : (factorDenominator r c hr0).1 = PowerSeries.subst z
        ((Matrix.det (1 - (Polynomial.X ^ r : ℚ[X]) •
          (LinearMap.toMatrix (Pi.basisFun ℚ (Fin c)) (Pi.basisFun ℚ (Fin c))
            (Representation.trivial ℚ G (Fin c → ℚ) h)).map Polynomial.C) : ℚ[X]) : PowerSeries ℚ) := by
      rw [hdetB]
      simp [factorDenominator, oneVarFactor]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hLogA, hLogB, hHist, ?_, ?_⟩
    · simpa [Nat.card_eq_fintype_card] using hdetA
    · exact hdetB
    · rw [(hBridgeA h 1 1).1]
      simpa [actualTraceA, Representation.character] using
        (LinearMap.trace_eq_matrix_trace ℚ (MonoidAlgebra.basis G ℚ)
          (Representation.leftRegular ℚ G h))
    · rw [(hBridgeB h r r).1]
      unfold actualTraceB
      rw [if_pos (by simp)]
      exact LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ (Fin c))
        (Representation.trivial ℚ G (Fin c → ℚ) h)
    · simpa [z_eq_pq] using hD1
    · simpa [z_eq_pq] using hD2
    · rw [(hBridgeA h r r).1]
      exact (hBridgeA h r r).2 (Or.inl (ne_of_gt hr))
    · simp [actualHB, Representation.trivial, Matrix.trace_one]

#print axioms single_cycle_det
#print axioms actual_ledger_collision

end
end D5.S3.Analytic.Dilation.ActualRegularLedgerCollision
