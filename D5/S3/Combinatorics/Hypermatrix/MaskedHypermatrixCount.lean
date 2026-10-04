/- GID: D5/S3/Combinatorics/Hypermatrix/MaskedHypermatrixCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hypermatrix/MaskedHypermatrixCount
   mirror-E: none(waiver:noncomputable-finite-field-enumeration)
   anchors: [mathlib/module/Mathlib]
   utility: none
   digest: The masked nondegenerate tensor count over every finite field. -/

import D5.S3.Combinatorics.Hypermatrix.MaskedTensorWeightedReduction

set_option autoImplicit false
open scoped BigOperators
open D5.S3.Combinatorics.Hypermatrix.MaskedFacesDefs

namespace D5.S3.Combinatorics.Hypermatrix.MaskedHypermatrixCount

open D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse
open D5.S3.Combinatorics.Permutation.CoupledOrderedRecovery
open D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction
open D5.S3.Combinatorics.Permutation.CoupledRepairedWeight

universe u

set_option maxHeartbeats 3000000 in
-- The proof combines induction and explicit finite coordinate constructions.
theorem result (F : Type u) [Field F] [Fintype F]
    (k : ℕ) (hk : 1 ≤ k) (lam mu : Fin k → ℕ)
    (hlam : Antitone lam) (hmu : Antitone mu)
    (hml : ∀ j, mu j ≤ lam j)
    (hlbound : ∀ j, lam j ≤ k - j.val)
    (hmbound : ∀ j, mu j < k - j.val) :

    Nat.card {T : Faces F k // Respects lam mu T ∧
        MvPolynomial.eval₂ (Int.castRingHom F)
          (fun v : TensorVariable k => if v.1 = 0 then T.1 v.2.1 v.2.2 else T.2 v.2.1 v.2.2)
          (coefficientPolynomial k) ≠ 0} =
        Fintype.card F ^ (k*k) * (Fintype.card F-1)^(2*k) *
          ∏ j : Fin k, qBracket (Fintype.card F) (k+1-j.val-lam j) *
            qBracket (Fintype.card F) (k-j.val-mu j) := by
  classical
  have coupledMaskedWeight
      (q k : ℕ) (lam mu : Fin k → ℕ)
      (hlam : Antitone lam) (hmu : Antitone mu)
      (hml : ∀ j, mu j ≤ lam j)
      (hlbound : ∀ j, lam j ≤ k-j.val)
      (hmbound : ∀ j, mu j < k-j.val) :
      (∑ S : Equiv.Perm (Fin (k+1)), ∑ p : Equiv.Perm (Fin k),
        if Eligible (fun j => k+1-lam j) (fun j => k+1-mu j) S p
        then q ^ (E (fun j => k+1-lam j) (fun j => k+1-mu j) S p).toNat else 0) =
      ∏ j : Fin k, qBracket q (k+1-j.val-lam j) * qBracket q (k-j.val-mu j) := by
    classical
    have prior_repairedEligible {n L B : ℕ} (hLB : L ≤ B) (hB : B ≤ n+1)
        (f g : Fin (n+1) → ℕ) (S : Equiv.Perm (Fin (n+2)))
        (p : Equiv.Perm (Fin (n+1))) (hf : Monotone f) (hg : Monotone g)
        (hfg : ∀ i, f i ≤ g i) (hf0 : f 0 = L+1)
        (hel : D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible f g S p) :
        let z := (D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.actualAlgorithms hLB hB).phi S p
        D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible
          (fun i => f i.succ - 1) (fun i => g i.succ - 1) z.1.1 z.1.2 := by
      dsimp only
      let ft := fun i : Fin n => f i.succ - 1
      let gt := fun i : Fin n => g i.succ - 1
      have hftgt : ∀ i, ft i ≤ gt i := fun i => Nat.sub_le_sub_right (hfg i.succ) 1
      have ordinary := D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.ordinary_eligibility
        f g S p hf hg hfg hel
      let s := D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.cut S (p 0).castSucc
      let hL := hLB.trans hB
      let theta := D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.lowWord S
        (Nat.add_le_add_right hL 1)
      let rho := D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.cut theta
        (theta.symm (Fin.last L))
      have preserve (u : Fin (n+1)) (T : ℕ) (hT : L ≤ T) :
          ((D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.replace s hL rho) u).val < T
            ↔ (s u).val < T := by
        by_cases hu : (s u).val < L
        · have hv : ((D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.replace s hL rho) u).val < L := by
            unfold D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.replace
            dsimp only [Equiv.trans_apply]
            rw [Equiv.Perm.ofSubtype_apply_of_mem
              (p := fun x : Fin (n+1) => x.val < L) (a := s u) _ hu]
            change (rho ((D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.lowWord s hL).symm ⟨(s u).val,hu⟩)).val < L
            exact (rho _).isLt
          exact iff_of_true (hv.trans_le hT) (hu.trans_le hT)
        · have he :
              (D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.replace s hL rho) u = s u := by
            unfold D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.replace
            dsimp only [Equiv.trans_apply]
            exact Equiv.Perm.ofSubtype_apply_of_not_mem _ hu
          rw [he]
      intro i
      have hlf : L ≤ ft i := by
        have h := hf (Fin.zero_le i.succ)
        dsimp [ft]
        rw [hf0] at h
        omega
      have hlg : L ≤ gt i := hlf.trans (hftgt i)
      constructor
      · apply (preserve _ _ hlf).mpr
        exact (ordinary i).1
      · apply (preserve _ _ hlg).mpr
        exact (ordinary i).2
    have prior_terminalZero (f g : Fin 0 → ℕ) (S : Equiv.Perm (Fin 1))
        (p : Equiv.Perm (Fin 0)) :
        D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.E f g S p = 0 := by
      have hs : S = Equiv.refl (Fin 1) := by
        apply Equiv.ext
        intro x
        apply Fin.ext
        have h1 := (S x).isLt
        have h2 := x.isLt
        omega
      rw [hs]
      simp [D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.E,
        D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.I,
        D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.ForbiddenCount,
        List.ofFn_succ, D5.S1.Digit.Carry.ListInversions.inv]

    have scoped_live_step {n L B : ℕ} (hLB : L ≤ B) (hB : B ≤ n+1)
        (f g : Fin (n+1) → ℕ) (S : Equiv.Perm (Fin (n+2)))
        (p : Equiv.Perm (Fin (n+1))) (hf : Monotone f) (hg : Monotone g)
        (hfg : ∀ i, f i ≤ g i) (hbound : ∀ i, g i ≤ n+2)
        (hf0 : f 0 = L+1) (hg0 : g 0 = B+1)
        (hel : D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible f g S p)
        (q : ℕ) :
        let z := (D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.actualAlgorithms hLB hB).phi S p
        q ^ (D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.E f g S p).toNat =
          q ^ (D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.E
            (fun i => f i.succ - 1) (fun i => g i.succ - 1) z.1.1 z.1.2).toNat *
            q ^ z.2.1 * q ^ z.2.2 := by
      classical
      have weightNonnegative (N : ℕ) :
          ∀ (f g : Fin N → ℕ) (S : Equiv.Perm (Fin (N+1)))
            (p : Equiv.Perm (Fin N)), Monotone f → Monotone g →
            (∀ i, f i ≤ g i) → (∀ i, g i ≤ N+1) →
            D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible f g S p →
            0 ≤ D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.E f g S p := by
        induction N with
        | zero =>
          intro f g S p hf hg hfg hbound hel
          rw [prior_terminalZero f g S p]
        | succ n ih =>
          intro f g S p hf hg hfg hbound hel
          let L := f 0 - 1
          let B := g 0 - 1
          have hLB : L ≤ B := Nat.sub_le_sub_right (hfg 0) 1
          have hB : B ≤ n+1 := by have h := hbound 0; dsimp [B]; omega
          have hfpos : 1 ≤ f 0 := by have h := (hel 0).1; omega
          have hgpos : 1 ≤ g 0 := hfpos.trans (hfg 0)
          have hf0 : f 0 = L+1 := by dsimp [L]; omega
          have hg0 : g 0 = B+1 := by dsimp [B]; omega
          let alg := D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.actualAlgorithms hLB hB
          let z := alg.phi S p
          let ft := fun i : Fin n => f i.succ - 1
          let gt := fun i : Fin n => g i.succ - 1
          have hft : Monotone ft := fun i j hij =>
            Nat.sub_le_sub_right (hf (Fin.succ_le_succ_iff.mpr hij)) 1
          have hgt : Monotone gt := fun i j hij =>
            Nat.sub_le_sub_right (hg (Fin.succ_le_succ_iff.mpr hij)) 1
          have hftgt : ∀ i, ft i ≤ gt i := fun i => Nat.sub_le_sub_right (hfg i.succ) 1
          have hgtbound : ∀ i, gt i ≤ n+1 := by
            intro i
            have h := hbound i.succ
            dsimp [gt]
            omega
          have ordinary :=
            D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.ordinary_eligibility
              f g S p hf hg hfg hel
          have repaired := prior_repairedEligible hLB hB f g S p hf hg hfg hf0 hel
          have hn := ih ft gt z.1.1 z.1.2 hft hgt hftgt hgtbound repaired
          have hw := D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.actual_repaired_weight
            hLB hB f g S p hf hg hfg hf0 hg0 hel
          change D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.E f g S p =
            D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.E ft gt z.1.1 z.1.2 +
              (z.2.1 : ℤ) + (z.2.2 : ℤ) at hw
          omega
      have coupledPowerStep {n L B : ℕ} (hLB : L ≤ B) (hB : B ≤ n+1)
          (f g : Fin (n+1) → ℕ) (S : Equiv.Perm (Fin (n+2)))
          (p : Equiv.Perm (Fin (n+1))) (hf : Monotone f) (hg : Monotone g)
          (hfg : ∀ i, f i ≤ g i) (hbound : ∀ i, g i ≤ n+2)
          (hf0 : f 0 = L+1) (hg0 : g 0 = B+1)
          (hel : D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible f g S p)
          (q : ℕ) :
          let z := (D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.actualAlgorithms hLB hB).phi S p
          q ^ (D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.E f g S p).toNat =
            q ^ (D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.E
              (fun i => f i.succ - 1) (fun i => g i.succ - 1) z.1.1 z.1.2).toNat *
              q ^ z.2.1 * q ^ z.2.2 := by
        let z := (D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.actualAlgorithms hLB hB).phi S p
        let ft := fun i : Fin n => f i.succ - 1
        let gt := fun i : Fin n => g i.succ - 1
        have hft : Monotone ft := fun i j hij =>
          Nat.sub_le_sub_right (hf (Fin.succ_le_succ_iff.mpr hij)) 1
        have hgt : Monotone gt := fun i j hij =>
          Nat.sub_le_sub_right (hg (Fin.succ_le_succ_iff.mpr hij)) 1
        have hftgt : ∀ i, ft i ≤ gt i := fun i => Nat.sub_le_sub_right (hfg i.succ) 1
        have hgtbound : ∀ i, gt i ≤ n+1 := by
          intro i
          have h := hbound i.succ
          dsimp [gt]
          omega
        have ht := prior_repairedEligible hLB hB f g S p hf hg hfg hf0 hel
        have hn := weightNonnegative n ft gt z.1.1 z.1.2 hft hgt hftgt hgtbound ht
        have hw := D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.actual_repaired_weight
          hLB hB f g S p hf hg hfg hf0 hg0 hel
        have hexp : (D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.E f g S p).toNat =
            (D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.E ft gt z.1.1 z.1.2).toNat +
              z.2.1 + z.2.2 := by
          change D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.E f g S p =
            D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.E ft gt z.1.1 z.1.2 +
              (z.2.1 : ℤ) + (z.2.2 : ℤ) at hw
          omega
        change q ^ (D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.E f g S p).toNat = _
        rw [hexp, pow_add, pow_add]
      exact coupledPowerStep hLB hB f g S p hf hg hfg hbound hf0 hg0 hel q

    have scoped_inverse_eligibility {n L B : ℕ} (hLB : L ≤ B) (hB : B ≤ n+1)
        (f g : Fin (n+1) → ℕ) (hf : Monotone f) (hg : Monotone g)
        (hfg : ∀ i, f i ≤ g i) (hf0 : f 0 = L+1) (hg0 : g 0 = B+1)
        (sd : Equiv.Perm (Fin (n+1))) (p : Equiv.Perm (Fin n))
        (d : Fin (L+1)) (b : Fin B)
        (htail : D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible
          (fun i => f i.succ - 1) (fun i => g i.succ - 1) sd p) :
        let z := (D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.actualAlgorithms hLB hB).psi sd p d b
        D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible f g z.1 z.2 := by
      classical
      have inverseEligible {n L B : ℕ} (hLB : L ≤ B) (hB : B ≤ n+1)
          (f g : Fin (n+1) → ℕ) (hf : Monotone f) (hg : Monotone g)
          (hfg : ∀ i, f i ≤ g i) (hf0 : f 0 = L+1) (hg0 : g 0 = B+1)
          (sd : Equiv.Perm (Fin (n+1))) (p : Equiv.Perm (Fin n))
          (d : Fin (L+1)) (b : Fin B)
          (htail : D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible
            (fun i => f i.succ - 1) (fun i => g i.succ - 1) sd p) :
          let z := (D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.actualAlgorithms hLB hB).psi sd p d b
          D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible f g z.1 z.2 := by
        let hL := hLB.trans hB
        let rho := D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.lowWord sd hL
        let theta := D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.put rho (Fin.last L)
          ⟨L-d.val, by omega⟩
        let t := (D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.slotOrder sd hB b).val
        let j := (Finset.univ.filter (fun u : Fin (n+1) => u < t ∧ (sd u).val < L)).card
        have hj : j ≤ L := by
          let lo := Finset.univ.filter (fun u : Fin (n+1) => (sd u).val < L)
          have hc : lo.card = L := by
            have he := Fintype.card_congr
              (D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.slotOrder sd hL).toEquiv
            simpa [D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.Slots,
              Fintype.card_subtype, lo] using he.symm
          apply hc ▸ Finset.card_le_card
            (show (Finset.univ.filter (fun u : Fin (n+1) => u < t ∧ (sd u).val < L)) ⊆ lo from ?_)
          intro u hu
          simp only [lo, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
          exact hu.2
        let aLow := theta ⟨j, by omega⟩
        let eta := D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.cut theta ⟨j, by omega⟩
        let s := D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.replace sd hL eta
        let a : Fin (n+2) := Fin.castLE (Nat.add_le_add_right hL 1) aLow
        let S := D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.put s a t.castSucc
        let P := D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.put p t 0
        have preserve (u : Fin (n+1)) (T : ℕ) (hT : L ≤ T) : (s u).val < T ↔ (sd u).val < T := by
          by_cases hu : (sd u).val < L
          · have hv : (s u).val < L := by
              dsimp [s, D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.replace]
              rw [Equiv.Perm.ofSubtype_apply_of_mem
                (p := fun x : Fin (n+1) => x.val < L) (a := sd u) _ hu]
              change (eta ((D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.lowWord sd hL).symm ⟨(sd u).val,hu⟩)).val < L
              exact (eta _).isLt
            exact iff_of_true (hv.trans_le hT) (hu.trans_le hT)
          · have he : s u = sd u := by
              dsimp [s, D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.replace]
              exact Equiv.Perm.ofSubtype_apply_of_not_mem _ hu
            rw [he]
        have ha : a.val < f 0 := by
          change aLow.val < f 0
          rw [hf0]
          exact aLow.isLt
        have hat (i : Fin (n+1)) : a.val < g i :=
          (ha.trans_le (hfg 0)).trans_le (hg (Fin.zero_le i))
        have hst : (s t).val < B := (preserve t B hLB).mpr
          (D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.slotOrder sd hB b).property
        have hsel : D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible
            (fun i => f i.succ - 1) (fun i => g i.succ - 1) s p := by
          intro i
          have hlf : L ≤ f i.succ - 1 := by have h := hf (Fin.zero_le i.succ); rw [hf0] at h; omega
          have hlg : L ≤ g i.succ - 1 := hlf.trans (Nat.sub_le_sub_right (hfg i.succ) 1)
          exact ⟨(preserve _ _ hlf).mpr (htail i).1, (preserve _ _ hlg).mpr (htail i).2⟩
        have lift (u : Fin (n+1)) : S (t.castSucc.succAbove u) = a.succAbove (s u) := by
          simp [S, D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.put]
        have raiseBound (v : Fin (n+1)) (T : ℕ) (hv : v.val < T-1) : (a.succAbove v).val < T := by
          by_cases h : v.castSucc < a
          · rw [Fin.succAbove_of_castSucc_lt _ _ h]
            simp only [Fin.val_castSucc]
            omega
          · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt h)]
            simp only [Fin.val_succ]
            omega
        change D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible f g S P
        intro i
        refine Fin.cases ?_ (fun v => ?_) i
        · have hp : P 0 = t := by simp [P, D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.put]
          rw [hp]
          constructor
          · simpa [S, D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.put] using ha
          · have he : t.succ = t.castSucc.succAbove t := (Fin.succAbove_castSucc_self t).symm
            rw [he, lift]
            have hv : (s t).val < g 0 - 1 := by rw [hg0]; simpa using hst
            exact raiseBound _ _ hv
        · have hp : P v.succ = t.succAbove (p v) := by
            change (finSuccEquiv' t).symm ((Equiv.optionCongr p) ((finSuccEquiv' 0) v.succ)) = _
            rw [← Fin.succAbove_zero_apply v, finSuccEquiv'_succAbove]
            rfl
          rw [hp]
          constructor
          · rw [← Fin.castSucc_succAbove_castSucc, lift]
            exact raiseBound _ _ (hsel v).1
          · by_cases he : (p v).succ = t
            · have hbefore : (p v).castSucc < t := by rw [← he]; exact Fin.castSucc_lt_succ
              rw [Fin.succAbove_of_castSucc_lt _ _ hbefore, Fin.succ_castSucc, he]
              have hs : S t.castSucc = a := by simp [S, D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse.put]
              rw [hs]
              exact hat v.succ
            · have hpos : (t.succAbove (p v)).succ = t.castSucc.succAbove (p v).succ := by
                apply Fin.ext
                simp only [Fin.succAbove, Fin.val_succ, Fin.val_castSucc, Fin.lt_def, apply_ite Fin.val]
                split_ifs <;> have hv := (p v).isLt <;> have ht := t.isLt <;>
                  have hne : (p v).val+1 ≠ t.val := fun hh => he (Fin.ext hh) <;> omega
              rw [hpos, lift]
              exact raiseBound _ _ (hsel v).2
      exact inverseEligible hLB hB f g hf hg hfg hf0 hg0 sd p d b htail

    have rightComposition {n L B : Nat} (hLB : L ≤ B) (hB : B ≤ n+1)
        (sd : Equiv.Perm (Fin (n+1))) (p : Equiv.Perm (Fin n))
        (d : Fin (L+1)) (b : Fin B) :
        let z := (actualAlgorithms hLB hB).psi sd p d b
        (actualAlgorithms hLB hB).phi z.1 z.2 = ((sd,p),(d.val,b.val)) := by
      classical
      have put_at {m : Nat} (w : Equiv.Perm (Fin m)) (a t : Fin (m+1)) :
          put w a t t = a := by simp [put]
      have put_lift {m : Nat} (w : Equiv.Perm (Fin m)) (a t : Fin (m+1)) (u : Fin m) :
          put w a t (t.succAbove u) = a.succAbove (w u) := by simp [put]
      have cut_put {m : Nat} (w : Equiv.Perm (Fin m)) (a t : Fin (m+1)) :
          cut (put w a t) t = w := by
        apply Equiv.ext
        intro u
        apply (Fin.strictMono_succAbove a).injective
        have hh := (finSuccAboveEquiv ((put w a t) t)).apply_symm_apply
          ((Equiv.subtypeEquiv (put w a t) (by intro x; exact (put w a t).injective.ne_iff.symm))
            ((finSuccAboveEquiv t) u))
        have he := congrArg Subtype.val hh
        change ((put w a t) t).succAbove ((cut (put w a t) t) u) =
          put w a t (t.succAbove u) at he
        simpa only [put_at,put_lift] using he
      have cut_unique {m : Nat} (w v : Equiv.Perm (Fin (m+1))) (t : Fin (m+1))
          (hat : w t = v t) (hcut : cut w t = cut v t) : w = v := by
        apply Equiv.ext
        intro x
        by_cases hx : x = t
        · simpa only [hx] using hat
        · obtain ⟨u,hu⟩ := (finSuccAboveEquiv t).surjective ⟨x,hx⟩
          have hux : t.succAbove u = x := congrArg Subtype.val hu
          have lift (v : Equiv.Perm (Fin (m+1))) :
              (v t).succAbove ((cut v t) u) = v (t.succAbove u) := by
            have hh := (finSuccAboveEquiv (v t)).apply_symm_apply
              ((Equiv.subtypeEquiv v (by intro x; exact v.injective.ne_iff.symm))
                ((finSuccAboveEquiv t) u))
            exact congrArg Subtype.val hh
          rw [← hux, ← lift w, ← lift v, hat, hcut]
      have preserve {m T : Nat} (w : Equiv.Perm (Fin m)) (hT : T ≤ m)
          (rho : Equiv.Perm (Fin T)) (u : Fin m) (R : Nat) (hR : T ≤ R) :
          ((replace w hT rho) u).val < R ↔ (w u).val < R := by
        by_cases hu : (w u).val < T
        · have hr : ((replace w hT rho) u).val < T := by
            dsimp [replace]
            rw [Equiv.Perm.ofSubtype_apply_of_mem
              (p := fun x : Fin m => x.val < T) (a := w u) _ hu]
            exact ((Equiv.permCongr (Fin.castLEOrderIso hT).toEquiv
              ((lowWord w hT).symm.trans rho)) ⟨w u,hu⟩).property
          exact iff_of_true (hr.trans_le hR) (hu.trans_le hR)
        · have he : (replace w hT rho) u = w u := by
            dsimp [replace]
            exact Equiv.Perm.ofSubtype_apply_of_not_mem _ hu
          rw [he]
      have rank {m T : Nat} (w : Equiv.Perm (Fin m)) (hT : T ≤ m) (i : Fin T) :
          (Finset.univ.filter (fun u : Fin m => u < (slotOrder w hT i).val ∧ (w u).val < T)).card = i.val := by
        let e := slotOrder w hT
        let E : {u : Fin m // u < (e i).val ∧ (w u).val < T} ≃ {j : Fin T // j < i} :=
          { toFun := fun u => ⟨e.symm ⟨u.val,u.property.2⟩, by
              apply e.lt_iff_lt.mp
              rw [e.apply_symm_apply]
              exact u.property.1⟩
            invFun := fun j => ⟨(e j.val).val, e.lt_iff_lt.mpr j.property, (e j.val).property⟩
            left_inv := by
              intro u
              apply Subtype.ext
              change (e (e.symm ⟨u.val,u.property.2⟩)).val = u.val
              exact congrArg Subtype.val (e.apply_symm_apply _)
            right_inv := by intro j; apply Subtype.ext; exact e.symm_apply_apply _ }
        have h := Fintype.card_congr E
        simp only [Fintype.card_subtype] at h
        have he : (Finset.univ.filter (fun x : Fin T => x < i)) = Finset.Iio i := by
          ext x
          simp
        rw [he,Fin.card_Iio] at h
        exact h
      let hL := hLB.trans hB
      let hA := Nat.add_le_add_right hL 1
      let rho := lowWord sd hL
      let q : Fin (L+1) := ⟨L-d.val,by omega⟩
      let theta := put rho (Fin.last L) q
      let t := (slotOrder sd hB b).val
      let j := (Finset.univ.filter (fun u : Fin (n+1) => u < t ∧ (sd u).val < L)).card
      have hj : j ≤ L := by
        let lo := Finset.univ.filter (fun u : Fin (n+1) => (sd u).val < L)
        have hc : lo.card = L := by
          have hh := Fintype.card_congr (slotOrder sd hL).toEquiv.symm
          simpa [Slots,Fintype.card_subtype,lo] using hh
        apply hc ▸ Finset.card_le_card
          (show (Finset.univ.filter (fun u : Fin (n+1) => u < t ∧ (sd u).val < L)) ⊆ lo from ?_)
        intro u hu
        simp only [lo,Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
        exact hu.2
      let jf : Fin (L+1) := ⟨j,by omega⟩
      let aLow := theta jf
      let eta := cut theta jf
      let s := replace sd hL eta
      let a : Fin (n+2) := Fin.castLE hA aLow
      let S := put s a t.castSucc
      let P := put p t 0
      have hP : P 0 = t := put_at p t 0
      have hcutS : cut S t.castSucc = s := cut_put s a t.castSucc
      have hcutP : cut P 0 = p := cut_put p t 0
      have ha : (S t.castSucc).val < L+1 := by
        rw [put_at]
        exact aLow.isLt
      let so := slotOrder S hA
      let r := so.symm ⟨t.castSucc,ha⟩
      have hsor : so r = ⟨t.castSucc,ha⟩ := so.apply_symm_apply _
      have theta_at : lowWord S hA r = aLow := by
        apply Fin.ext
        change (S (so r).val).val = aLow.val
        rw [hsor,put_at]
        rfl
      have low_before (u : Fin (n+1)) (hu : u < t) :
          (S u.castSucc).val < L+1 ↔ (sd u).val < L := by
        have hv := put_lift s a t.castSucc u
        rw [Fin.succAbove_of_castSucc_lt _ _ (show u.castSucc < t.castSucc from hu)] at hv
        rw [hv]
        have hav : a.val < L+1 := aLow.isLt
        have hpre := preserve sd hL eta u L le_rfl
        change (s u).val < L ↔ (sd u).val < L at hpre
        rw [← hpre]
        by_cases h : (s u).castSucc < a
        · rw [Fin.succAbove_of_castSucc_lt _ _ h]
          have hval : (s u).val < a.val := h
          simp only [Fin.val_castSucc]
          omega
        · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt h)]
          simp only [Fin.val_succ]
          omega
      have hprefix : (Finset.univ.filter (fun u : Fin (n+2) =>
          u < t.castSucc ∧ (S u).val < L+1)).card = j := by
        dsimp only [j]
        symm
        apply Finset.card_bij (fun u _ => u.castSucc)
        · intro u hu
          simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
          exact ⟨hu.1,(low_before u hu.1).mpr hu.2⟩
        · intro u hu v hv he
          exact Fin.castSucc_injective _ he
        · intro v hv
          simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hv
          let u : Fin (n+1) := ⟨v.val,by have hval : v.val < t.val := hv.1; omega⟩
          have huc : u.castSucc = v := Fin.ext rfl
          have hut : u < t := hv.1
          refine ⟨u,?_,huc⟩
          simp only [Finset.mem_filter,Finset.mem_univ,true_and]
          exact ⟨hut,(low_before u hut).mp (huc ▸ hv.2)⟩
      have hrj : r = jf := by
        apply Fin.ext
        have hr := rank S hA r
        rw [hsor] at hr
        exact hr.symm.trans hprefix
      have recover := shared_ordered_recovery (@cut) (@slotOrder) (@lowWord) (@replace)
        (by intros; rfl) (by intros; rfl) (by intros; rfl)
      have hword : lowWord s hL = eta := (recover.2 sd hL eta).1
      have hdelete := recover.1 hL S t.castSucc ha
      change lowWord (cut S t.castSucc) hL = cut (lowWord S hA) r at hdelete
      rw [hcutS,hword,hrj] at hdelete
      have htheta : lowWord S hA = theta := by
        apply cut_unique _ _ jf
        · rw [hrj] at theta_at
          exact theta_at
        · exact hdelete.symm
      have hq : (lowWord S hA).symm (Fin.last L) = q := by
        rw [htheta]
        apply theta.injective
        rw [theta.apply_symm_apply]
        exact (put_at rho (Fin.last L) q).symm
      have hrho : cut (lowWord S hA) ((lowWord S hA).symm (Fin.last L)) = rho := by
        rw [hq,htheta]
        exact cut_put rho (Fin.last L) q
      have hsback : replace s hL rho = sd := (recover.2 sd hL eta).2
      have hb : (Finset.univ.filter (fun u : Fin (n+1) => u < t ∧ (s u).val < B)).card = b.val := by
        rw [← rank sd hB b]
        apply congrArg Finset.card
        ext u
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        exact and_congr_right (fun _ => preserve sd hL eta u B hLB)
      change ((replace (cut S (P 0).castSucc) hL
        (cut (lowWord S hA) ((lowWord S hA).symm (Fin.last L))),cut P 0),
        L-((lowWord S hA).symm (Fin.last L)).val,
        (Finset.univ.filter (fun u : Fin (n+1) => u < P 0 ∧ ((cut S (P 0).castSucc) u).val < B)).card) = _
      rw [hP,hcutS,hcutP,hrho,hsback,hq,hb]
      have hd : L-q.val = d.val := by dsimp [q]; have h := d.isLt; omega
      rw [hd]
    let W (N : ℕ) (f g : Fin N → ℕ) :=
      ∑ S : Equiv.Perm (Fin (N+1)), ∑ p : Equiv.Perm (Fin N),
        if Eligible f g S p then q ^ (E f g S p).toNat else 0
    have eligibleSum (N : ℕ) (f g : Fin N → ℕ) :
        W N f g = ∑ x : {z : Equiv.Perm (Fin (N+1)) × Equiv.Perm (Fin N) //
          Eligible f g z.1 z.2}, q ^ (E f g x.val.1 x.val.2).toNat := by
      dsimp only [W]
      rw [← Fintype.sum_prod_type']
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero]
      exact Finset.sum_subtype _ (by simp) _
    have recurrence {n L B : ℕ} (hLB : L ≤ B) (hB : B ≤ n+1)
        (f g : Fin (n+1) → ℕ) (hf : Monotone f) (hg : Monotone g)
        (hfg : ∀ i, f i ≤ g i) (hbound : ∀ i, g i ≤ n+2)
        (hf0 : f 0 = L+1) (hg0 : g 0 = B+1) :
        W (n+1) f g = W n (fun i => f i.succ-1) (fun i => g i.succ-1) *
          qBracket q (L+1) * qBracket q B := by
      let ft : Fin n → ℕ := fun i => f i.succ-1
      let gt : Fin n → ℕ := fun i => g i.succ-1
      let alg := actualAlgorithms hLB hB
      let Source := {z : Equiv.Perm (Fin (n+2)) × Equiv.Perm (Fin (n+1)) //
        Eligible f g z.1 z.2}
      let Tail := {z : Equiv.Perm (Fin (n+1)) × Equiv.Perm (Fin n) //
        Eligible ft gt z.1 z.2}
      let Target := Tail × Fin (L+1) × Fin B
      let forward (x : Source) : Target := by
        let z := alg.phi x.val.1 x.val.2
        have hleft := actual_full_left_composition hLB hB x.val.1 x.val.2
          (hf0 ▸ (x.property 0).1) (hg0 ▸ (x.property 0).2)
        exact (⟨z.1, prior_repairedEligible hLB hB f g x.val.1 x.val.2 hf hg hfg hf0 x.property⟩,
          ⟨z.2.1,hleft.choose⟩, ⟨z.2.2,hleft.choose_spec.choose⟩)
      let backward (y : Target) : Source :=
        ⟨alg.psi y.1.val.1 y.1.val.2 y.2.1 y.2.2,
          scoped_inverse_eligibility hLB hB f g hf hg hfg hf0 hg0
            y.1.val.1 y.1.val.2 y.2.1 y.2.2 y.1.property⟩
      have left : Function.LeftInverse backward forward := by
        intro x
        apply Subtype.ext
        exact (actual_full_left_composition hLB hB x.val.1 x.val.2
          (hf0 ▸ (x.property 0).1) (hg0 ▸ (x.property 0).2)).choose_spec.choose_spec
      have right : Function.RightInverse backward forward := by
        intro y
        have hr := rightComposition hLB hB y.1.val.1 y.1.val.2 y.2.1 y.2.2
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg Prod.fst hr
        · apply Prod.ext
          · apply Fin.ext
            exact congrArg (fun z => z.2.1) hr
          · apply Fin.ext
            exact congrArg (fun z => z.2.2) hr
      let equiv : Source ≃ Target := ⟨forward,backward,left,right⟩
      have reindex : (∑ x : Source, q ^ (E f g x.val.1 x.val.2).toNat) =
          ∑ y : Target, q ^ (E ft gt y.1.val.1 y.1.val.2).toNat *
            q ^ y.2.1.val * q ^ y.2.2.val := by
        apply Fintype.sum_equiv equiv
        intro x
        exact scoped_live_step hLB hB f g x.val.1 x.val.2 hf hg hfg hbound hf0 hg0 x.property q
      rw [eligibleSum, reindex]
      change (∑ y : Tail × (Fin (L+1) × Fin B), q ^ (E ft gt y.1.val.1 y.1.val.2).toNat *
        q ^ y.2.1.val * q ^ y.2.2.val) = _
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      rw [← eligibleSum]
      have digits (r : ℕ) : (∑ e : Fin r, q ^ e.val) = qBracket q r :=
        Fin.sum_univ_eq_sum_range (fun e => q ^ e) r
      rw [digits, digits]
    have iteration (N : ℕ) : ∀ (f g : Fin N → ℕ),
        Monotone f → Monotone g → (∀ i, f i ≤ g i) → (∀ i, g i ≤ N+1) →
        (∀ i, i.val+1 ≤ f i) → (∀ i, i.val+2 ≤ g i) →
        W N f g = ∏ i : Fin N, qBracket q (f i-i.val) * qBracket q (g i-(i.val+1)) := by
      induction N with
      | zero =>
        intro f g hf hg hfg hb hfmin hgmin
        dsimp only [W]
        have eligible (S : Equiv.Perm (Fin 1)) (p : Equiv.Perm (Fin 0)) : Eligible f g S p := by
          intro i; exact Fin.elim0 i
        simp only [eligible, if_true, prior_terminalZero, Int.toNat_zero, pow_zero]
        simp
      | succ n ih =>
        intro f g hf hg hfg hb hfmin hgmin
        let L := f 0-1
        let B := g 0-1
        have hf0 : f 0 = L+1 := by have h := hfmin 0; simp only [Fin.val_zero] at h; dsimp [L]; omega
        have hg0 : g 0 = B+1 := by have h := hgmin 0; simp only [Fin.val_zero] at h; dsimp [B]; omega
        have hLB : L ≤ B := Nat.sub_le_sub_right (hfg 0) 1
        have hB : B ≤ n+1 := by have h := hb 0; dsimp [B]; omega
        let ft : Fin n → ℕ := fun i => f i.succ-1
        let gt : Fin n → ℕ := fun i => g i.succ-1
        have hft : Monotone ft := fun i j hij => Nat.sub_le_sub_right (hf (Fin.succ_le_succ_iff.mpr hij)) 1
        have hgt : Monotone gt := fun i j hij => Nat.sub_le_sub_right (hg (Fin.succ_le_succ_iff.mpr hij)) 1
        have hftgt : ∀ i, ft i ≤ gt i := fun i => Nat.sub_le_sub_right (hfg i.succ) 1
        have hgtbound : ∀ i, gt i ≤ n+1 := by intro i; have h := hb i.succ; dsimp [gt]; omega
        have hftmin : ∀ i, i.val+1 ≤ ft i := by
          intro i; have h := hfmin i.succ; dsimp [ft] ; simp only [Fin.val_succ] at h; omega
        have hgtmin : ∀ i, i.val+2 ≤ gt i := by
          intro i; have h := hgmin i.succ; dsimp [gt] ; simp only [Fin.val_succ] at h; omega
        rw [recurrence hLB hB f g hf hg hfg hb hf0 hg0]
        rw [ih ft gt hft hgt hftgt hgtbound hftmin hgtmin]
        rw [Fin.prod_univ_succ]
        simp only [Fin.val_zero, Nat.sub_zero, hf0, hg0, Nat.add_sub_cancel]
        have factors (i : Fin n) :
            qBracket q (ft i-i.val) * qBracket q (gt i-(i.val+1)) =
            qBracket q (f i.succ-i.succ.val) * qBracket q (g i.succ-(i.succ.val+1)) := by
          dsimp [ft,gt]
          simp only [Nat.sub_sub]
          congr 2 <;> omega
        simp_rw [factors]
        ring
    have hf : Monotone (fun j => k+1-lam j) := fun i j hij => Nat.sub_le_sub_left (hlam hij) _
    have hg : Monotone (fun j => k+1-mu j) := fun i j hij => Nat.sub_le_sub_left (hmu hij) _
    have hfg : ∀ j, k+1-lam j ≤ k+1-mu j := fun j => Nat.sub_le_sub_left (hml j) _
    have hb : ∀ j, k+1-mu j ≤ k+1 := fun j => Nat.sub_le _ _
    have hfmin : ∀ j : Fin k, j.val+1 ≤ k+1-lam j := by
      intro j; have h := hlbound j; have hj := j.isLt; omega
    have hgmin : ∀ j : Fin k, j.val+2 ≤ k+1-mu j := by
      intro j; have h := hmbound j; have hj := j.isLt; omega
    change W k (fun j => k+1-lam j) (fun j => k+1-mu j) = _
    rw [iteration k _ _ hf hg hfg hb hfmin hgmin]
    apply Finset.prod_congr rfl
    intro j hj
    congr 2 <;> omega
  have coefficient_determinant_eq_zero_of_pencil_kernel
      {K : Type u} [Field K] {k : ℕ} (_hk : 1 ≤ k)
      (T : Faces K k) {a b : K} (hab : a ≠ 0 ∨ b ≠ 0)
      {z : Fin k → K} (hz : z ≠ 0)
      (hker : (a • T.1 + b • T.2).mulVec z = 0) :
      (coefficientMatrix T.1 T.2).det = 0 := by
    classical
    have htranspose : (coefficientMatrix T.1 T.2).transpose.mulVec
        (coefficientWeight a b z) = 0 := by
      funext col
      rcases col with ⟨s, r⟩
      simp only [Matrix.mulVec, dotProduct, coefficientMatrix, coefficientWeight,
        Matrix.transpose_apply]
      change (∑ i : CoeffIndex k,
          ((if i.2.val = s.val then T.1 r i.1 else 0) +
            if i.2.val = s.val + 1 then T.2 r i.1 else 0) *
            (z i.1 * a ^ (k - i.2.val) * b ^ i.2.val)) = 0
      rw [Fintype.sum_prod_type]
      have hcast (t : Fin (k + 1)) : t.val = s.val ↔ t = s.castSucc := by
        simp [Fin.ext_iff]
      have hsucc (t : Fin (k + 1)) : t.val = s.val + 1 ↔ t = s.succ := by
        simp [Fin.ext_iff, Fin.val_succ]
      simp only [hcast, hsucc, add_mul, Finset.sum_add_distrib,
        ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have hs : k - s.val = (k - (s.val + 1)) + 1 := by omega
      have hr := congrFun hker r
      simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, Pi.zero_apply] at hr
      calc
        _ = (a ^ (k - (s.val + 1)) * b ^ s.val) *
            (∑ j, (a * T.1 r j + b * T.2 r j) * z j) := by
              rw [Finset.mul_sum, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro j _
              simp only [Fin.val_castSucc, Fin.val_succ]
              rw [hs, pow_succ, pow_succ]
              ring
        _ = 0 := by rw [hr, mul_zero]
    obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
      by_contra! hh
      apply hz
      funext j
      exact hh j
    have hw : ∃ i, coefficientWeight a b z i ≠ 0 := by
      rcases hab with ha | hb
      · refine ⟨(j, 0), ?_⟩
        simp only [coefficientWeight, Fin.val_zero, Nat.sub_zero, pow_zero, mul_one]
        exact mul_ne_zero hj (pow_ne_zero k ha)
      · refine ⟨(j, Fin.last k), ?_⟩
        simp only [coefficientWeight, Fin.val_last, Nat.sub_self, pow_zero, mul_one]
        exact mul_ne_zero hj (pow_ne_zero k hb)
    obtain ⟨i, hi⟩ := hw
    have hd := Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
      htranspose (mem_nonZeroDivisors_of_ne_zero hi)
    simpa only [Matrix.det_transpose] using hd
  have standard_coefficient_determinant_ne_zero
      {K : Type u} [Field K] {k : ℕ} (hk : 1 ≤ k) :
      (coefficientMatrix (E0 K k) (E1 K k)).det ≠ 0 := by
    classical
    let D := coefficientMatrix (E0 K k) (E1 K k)
    have hkernel (v : CoeffIndex k → K) (hv : D.mulVec v = 0) : v = 0 := by
      have hrow (j : Fin k) (t : Fin (k+1)) :
          (∑ s : Fin k, if t.val = s.val then v (s,j.castSucc) else 0) +
          (∑ s : Fin k, if t.val = s.val+1 then v (s,j.succ) else 0) = 0 := by
        have h := congrFun hv (j,t)
        simpa [D, coefficientMatrix, E0, E1, Matrix.mulVec, dotProduct,
          Fintype.sum_prod_type, add_mul, ite_mul, Finset.sum_add_distrib] using h
      have hstart (j : Fin k) : v (⟨0,by omega⟩,j.castSucc) = 0 := by
        have h := hrow j 0
        have he (s : Fin k) : 0 = s.val ↔ s = ⟨0,by omega⟩ := by
          simp [Fin.ext_iff, eq_comm]
        simpa [he] using h
      have hend (j : Fin k) : v (⟨k-1,by omega⟩,j.succ) = 0 := by
        have h := hrow j (Fin.last k)
        have hn (s : Fin k) : ¬k = s.val := by have h := s.isLt; omega
        have he (s : Fin k) : k = s.val+1 ↔ s = ⟨k-1,by omega⟩ := by
          rw [Fin.ext_iff]
          simp only [Fin.val_mk]
          have h := s.isLt
          omega
        simpa [hn,he] using h
      have hrec (j s t : Fin k) (hst : t.val = s.val+1) :
          v (t,j.castSucc) + v (s,j.succ) = 0 := by
        have h := hrow j t.castSucc
        have he (x : Fin k) : t.val = x.val ↔ x = t := by simp [Fin.ext_iff,eq_comm]
        have he' (x : Fin k) : t.val = x.val+1 ↔ x = s := by
          rw [Fin.ext_iff, hst]
          omega
        simpa [he,he'] using h
      have hearly : ∀ n : ℕ, ∀ hn : n < k, ∀ r : Fin (k+1),
          r.val + n < k → v (⟨n,hn⟩,r) = 0 := by
        intro n
        induction n with
        | zero =>
          intro hn r hr
          let j : Fin k := ⟨r.val,by omega⟩
          have hj : j.castSucc = r := Fin.ext rfl
          simpa only [hj] using hstart j
        | succ n ih =>
          intro hn r hr
          let j : Fin k := ⟨r.val,by omega⟩
          let s : Fin k := ⟨n,by omega⟩
          let t : Fin k := ⟨n+1,hn⟩
          have hj : j.castSucc = r := Fin.ext rfl
          have hi := ih (by omega) j.succ (by simp only [Fin.val_succ]; dsimp [j]; omega)
          have hh := hrec j s t rfl
          rw [hj, show v (s,j.succ) = 0 from hi, add_zero] at hh
          exact hh
      have hlate : ∀ n : ℕ, ∀ s : Fin k, k-1-s.val = n →
          ∀ r : Fin (k+1), k ≤ r.val+s.val → v (s,r) = 0 := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
          intro s hn r hr
          have hs := s.isLt
          have hr0 : 0 < r.val := by omega
          let j : Fin k := ⟨r.val-1,by have h := r.isLt; omega⟩
          have hj : j.succ = r := by apply Fin.ext; dsimp [j]; omega
          by_cases hsend : s.val = k-1
          · have he : s = ⟨k-1,by omega⟩ := Fin.ext hsend
            simpa only [hj, ← he] using hend j
          · let t : Fin k := ⟨s.val+1,by omega⟩
            have hi : v (t,j.castSucc) = 0 :=
              ih (k-1-t.val) (by dsimp [t]; omega) t rfl j.castSucc
                (by dsimp [t,j]; omega)
            have hh := hrec j s t rfl
            rw [hi, zero_add, hj] at hh
            exact hh
      funext i
      rcases i with ⟨s,r⟩
      by_cases hr : r.val+s.val < k
      · exact hearly s.val s.isLt r hr
      · exact hlate (k-1-s.val) s rfl r (by omega)
    have hi : Function.Injective D.mulVec := by
      intro x y hxy
      have hzero : D.mulVec (x-y) = 0 := by
        rw [Matrix.mulVec_sub, hxy, sub_self]
      exact sub_eq_zero.mp (hkernel (x-y) hzero)
    exact (Matrix.isUnit_iff_isUnit_det D |>.mp
      (Matrix.mulVec_injective_iff_isUnit.mp hi)).ne_zero
  have coefficient_right_covariance
      {F : Type u} [Field F] {k : ℕ}
      (M0 M1 : Matrix (Fin (k+1)) (Fin k) F)
      (B : Matrix (Fin k) (Fin k) F) :
      coefficientMatrix (M0 * B) (M1 * B) =
        Matrix.kronecker B.transpose (1 : Matrix (Fin (k+1)) (Fin (k+1)) F) *
          coefficientMatrix M0 M1 := by
    classical
    ext row col
    rcases row with ⟨j,t⟩
    rcases col with ⟨s,r⟩
    change (if t.val = s.val then ∑ l, M0 r l * B l j else 0) +
      (if t.val = s.val+1 then ∑ l, M1 r l * B l j else 0) =
      ∑ x : CoeffIndex k, (B x.1 j * (if t = x.2 then 1 else 0)) *
        ((if x.2.val = s.val then M0 r x.1 else 0) +
          (if x.2.val = s.val+1 then M1 r x.1 else 0))
    rw [Fintype.sum_prod_type]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h0 : t.val = s.val <;> by_cases h1 : t.val = s.val+1 <;>
      simp [h0,h1,mul_add,Finset.sum_add_distrib,mul_comm]

  have coefficient_left_covariance
      {F : Type u} [Field F] {k : ℕ}
      (M0 M1 : Matrix (Fin (k+1)) (Fin k) F)
      (A : Matrix (Fin (k+1)) (Fin (k+1)) F) :
      coefficientMatrix (A * M0) (A * M1) =
        coefficientMatrix M0 M1 *
          Matrix.kronecker (1 : Matrix (Fin k) (Fin k) F) A.transpose := by
    classical
    ext row col
    rcases row with ⟨j,t⟩
    rcases col with ⟨s,r⟩
    change (if t.val = s.val then ∑ l, A r l * M0 l j else 0) +
      (if t.val = s.val+1 then ∑ l, A r l * M1 l j else 0) =
      ∑ x : CoeffIndex k,
        ((if t.val = x.1.val then M0 x.2 j else 0) +
          (if t.val = x.1.val+1 then M1 x.2 j else 0)) *
          ((if x.1 = s then 1 else 0) * A r x.2)
    rw [Fintype.sum_prod_type]
    simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
    by_cases h0 : t.val = s.val <;> by_cases h1 : t.val = s.val+1 <;>
      simp [h0,h1,add_mul,Finset.sum_add_distrib,mul_comm]
  have coefficient_nonzero_implies_closureFullRank
      {F : Type u} [Field F] {k : ℕ} (hk : 1 ≤ k)
      (T : Faces F k) (hdet : (coefficientMatrix T.1 T.2).det ≠ 0) :
      ClosureFullRank T := by
    classical
    let f := algebraMap F (AlgebraicClosure F)
    have hmap : coefficientMatrix (T.1.map f) (T.2.map f) =
        (coefficientMatrix T.1 T.2).map f := by
      ext row col
      simp only [coefficientMatrix,Matrix.map_apply,map_add]
      split_ifs <;> simp
    have hmapped : (coefficientMatrix (T.1.map f) (T.2.map f)).det ≠ 0 := by
      rw [hmap]
      change (f.mapMatrix (coefficientMatrix T.1 T.2)).det ≠ 0
      rw [← RingHom.map_det]
      intro hzero
      apply hdet
      apply f.injective
      simpa only [map_zero] using hzero
    intro a b hab
    let M := a • T.1.map f + b • T.2.map f
    have hi : Function.Injective M.mulVecLin := by
      intro x y hxy
      by_contra hne
      have hz : x-y ≠ 0 := sub_ne_zero.mpr hne
      have hzero : M.mulVec (x-y) = 0 := by
        rw [Matrix.mulVec_sub]
        exact sub_eq_zero.mpr hxy
      exact hmapped (coefficient_determinant_eq_zero_of_pencil_kernel hk
        (T.1.map f,T.2.map f) hab hz hzero)
    change Module.finrank (AlgebraicClosure F) M.mulVecLin.range = k
    simpa only [Module.finrank_pi,Fintype.card_fin] using
      LinearMap.finrank_range_of_inj hi
  have original_faces_coefficient_nonzero_iff_closureFullRank
      (F : Type u) [Field F] (k : ℕ) (hk : 1 ≤ k) (T : Faces F k) :
      (coefficientMatrix T.1 T.2).det ≠ 0 ↔ ClosureFullRank T := by
    classical
    constructor
    · exact coefficient_nonzero_implies_closureFullRank hk T
    · intro hT
      have normalization := (PencilParameterFibers.pencil_parameter_fibers F k hk).1
      obtain ⟨A,B,h0,h1⟩ := normalization T hT
      rw [h0,h1, coefficient_right_covariance, coefficient_left_covariance,
        Matrix.det_mul,Matrix.det_mul]
      simp only [Matrix.kronecker,Matrix.det_kronecker]
      simp only [Matrix.det_transpose,Matrix.det_one,one_pow,mul_one,one_mul,
        Fintype.card_fin]
      exact mul_ne_zero
        (pow_ne_zero _ (Matrix.isUnits_det_units B).ne_zero)
        (mul_ne_zero (standard_coefficient_determinant_ne_zero hk)
          (pow_ne_zero _ (Matrix.isUnits_det_units A).ne_zero))
  have original_faces_coefficientPolynomial_nonzero_iff_closureFullRank
      (F : Type u) [Field F] (k : ℕ) (hk : 1 ≤ k) (T : Faces F k) :
      MvPolynomial.eval₂ (Int.castRingHom F)
        (fun v : TensorVariable k => if v.1 = 0 then T.1 v.2.1 v.2.2 else T.2 v.2.1 v.2.2)
        (coefficientPolynomial k) ≠ 0 ↔ ClosureFullRank T := by
    classical
    let f := MvPolynomial.eval₂Hom (Int.castRingHom F)
      (fun v : TensorVariable k => if v.1 = 0 then T.1 v.2.1 v.2.2 else T.2 v.2.1 v.2.2)
    have he : f (coefficientPolynomial k) = (coefficientMatrix T.1 T.2).det := by
      unfold coefficientPolynomial
      rw [RingHom.map_det]
      congr 1
      ext row col
      by_cases h0 : row.2.val = col.1.val <;>
        by_cases h1 : row.2.val = col.1.val+1 <;>
        simp [RingHom.mapMatrix_apply,coefficientMatrix,f,h0,h1]
    change f (coefficientPolynomial k) ≠ 0 ↔ ClosureFullRank T
    rw [he]
    exact original_faces_coefficient_nonzero_iff_closureFullRank F k hk T
  let equiv : {T : Faces F k // Respects lam mu T ∧
      MvPolynomial.eval₂ (Int.castRingHom F)
        (fun v : TensorVariable k => if v.1 = 0 then T.1 v.2.1 v.2.2 else T.2 v.2.1 v.2.2)
        (coefficientPolynomial k) ≠ 0} ≃ ActualCarrier F k lam mu :=
    Equiv.subtypeEquivRight (fun T =>
      and_congr_right (fun _ =>
        original_faces_coefficientPolynomial_nonzero_iff_closureFullRank F k hk T))
  rw [Nat.card_congr equiv]
  rw [MaskedTensorWeightedReduction.masked_tensor_weighted_reduction F k hk lam mu
    hlam hmu hml hlbound hmbound]
  rw [coupledMaskedWeight (Fintype.card F) k lam mu
    hlam hmu hml hlbound hmbound]

end D5.S3.Combinatorics.Hypermatrix.MaskedHypermatrixCount
