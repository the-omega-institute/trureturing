/- GID: D5/S3/Quantum/Fibers/SharedEnergyGapBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Fibers/SharedEnergyGapBound
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Labelled indecomposable zero-weight exponents have bounded degree. -/

import D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold

/-! Labelled zero-weight exponents in the fixed three-level basis. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Matrix

namespace D5.S3.Quantum.Fibers.SharedEnergyGapBound
open D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
open D5.S3.Quantum.Fibers.RealCopyConjugation

private def gaps (a A b B c C : ℕ) : Exponent := !![0,A,C; a,0,B; c,b,0]

private theorem gaps_degree (a A b B c C : ℕ) :
    degree (gaps a A b B c C) = a + A + b + B + c + C := by
  simp [degree, gaps, Fin.sum_univ_succ]
  omega

private theorem gaps_weight (m a A b B c C : ℕ) :
    weight m (gaps a A b B c C) =
      (a : ℤ)-A+((m : ℤ)-1)*((b : ℤ)-B)+(m : ℤ)*((c : ℤ)-C) := by
  simp [weight, gaps, energy, Fin.sum_univ_succ]
  ring

private theorem force_degree (m : ℕ) (alpha beta : Exponent)
    (h : Indecomposable m alpha) (hne : beta ≠ 0) (hle : beta ≤ alpha)
    (hw : weight m beta = 0) (hd : degree beta ≤ 2 * m - 1) : degree alpha ≤ 2 * m - 1 := by
  rcases h.2.2 beta hle hw with hz | he
  · exact (hne hz).elim
  · simpa only [he] using hd

private theorem gaps_nonzero (a A b B c C : ℕ) (hp : 0 < a + A + b + B + c + C) :
    gaps a A b B c C ≠ 0 := by
  intro h
  have hd := congrArg degree h
  rw [gaps_degree] at hd
  simp only [degree, Pi.zero_apply, Finset.sum_const_zero] at hd
  omega

private theorem oriented_bound (m : ℕ) (hm : 2 ≤ m) (a A b B C : ℕ)
    (h : Indecomposable m (gaps a A b B 0 C))
    (ha : a = 0 ∨ A = 0) (hb : b = 0 ∨ B = 0) :
    degree (gaps a A b B 0 C) ≤ 2 * m - 1 := by
  have hm₁ : 1 ≤ m := by omega
  have hm₂ : 1 ≤ m-1 := by omega
  have hsucc : m-1+1 = m := by omega
  have hw := h.2.1
  rw [gaps_weight] at hw
  have hn : a+(m-1)*b = A+(m-1)*B+m*C := by
    have hc : ((m-1 : ℕ) : ℤ) = (m : ℤ)-1 := by omega
    have he : (a : ℤ)+((m-1 : ℕ) : ℤ)*b =
        (A : ℤ)+((m-1 : ℕ) : ℤ)*B+(m : ℤ)*C := by
      rw [hc]
      linear_combination hw
    exact_mod_cast he
  by_cases haz : a = 0
  · subst a
    by_cases hbz : b = 0
    · subst b
      have hA : A = 0 := by omega
      have hB : B = 0 := by nlinarith
      have hC : C = 0 := by nlinarith
      subst A; subst B; subst C
      exact (h.1 (by ext i j; fin_cases i <;> fin_cases j <;> simp [gaps])).elim
    · have hbpos : 0 < b := by omega
      have hB : B = 0 := hb.resolve_left hbz
      subst B
      by_cases hC : m-1 ≤ C
      · have hbm : m ≤ b := by
          have hmul := Nat.mul_le_mul_left m hC
          by_contra! hbad
          have hmul' := Nat.mul_le_mul_left (m-1) (by omega : b ≤ m-1)
          nlinarith
        apply force_degree m _ (gaps 0 0 m 0 0 (m-1)) h
        · apply gaps_nonzero; omega
        · intro i j
          fin_cases i <;> fin_cases j <;> simp [gaps] <;> omega
        · rw [gaps_weight]
          simp only [Nat.cast_zero, Nat.cast_sub hm₁, Nat.cast_one]
          ring
        · rw [gaps_degree]
          omega
      · by_cases hCz : C = 0
        · subst C
          have hA : m-1 ≤ A := by nlinarith
          apply force_degree m _ (gaps 0 (m-1) 1 0 0 0) h
          · apply gaps_nonzero; omega
          · intro i j
            fin_cases i <;> fin_cases j <;> simp [gaps] <;> omega
          · rw [gaps_weight]
            simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_sub hm₁]
            ring
          · rw [gaps_degree]; omega
        · have hCpos : 0 < C := by omega
          have hbc : C+1 ≤ b := by
            by_contra! hbad
            have hmul := Nat.mul_le_mul_left (m-1) (by omega : b ≤ C)
            nlinarith
          have hsub : m-1-C+C = m-1 := Nat.sub_add_cancel (by omega)
          have hA : m-1-C ≤ A := by
            have hmul := Nat.mul_le_mul_left (m-1) hbc
            nlinarith
          apply force_degree m _ (gaps 0 (m-1-C) (C+1) 0 0 C) h
          · apply gaps_nonzero; omega
          · intro i j
            fin_cases i <;> fin_cases j <;> simp [gaps] <;> omega
          · rw [gaps_weight]
            have hcast : ((m-1-C : ℕ) : ℤ) = (m : ℤ)-1-C := by omega
            simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, hcast]
            ring
          · rw [gaps_degree]; omega
  · have hapos : 0 < a := by omega
    have hA : A = 0 := ha.resolve_left haz
    subst A
    by_cases hbz : b = 0
    · subst b
      by_cases hB : B = 0
      · subst B
        have hC : 1 ≤ C := by nlinarith
        have ham : m ≤ a := by nlinarith
        apply force_degree m _ (gaps m 0 0 0 0 1) h
        · apply gaps_nonzero; omega
        · intro i j
          fin_cases i <;> fin_cases j <;> simp [gaps] <;> omega
        · rw [gaps_weight]; simp
        · rw [gaps_degree]; omega
      · have hBpos : 0 < B := by omega
        have ha₁ : m-1 ≤ a := by nlinarith
        apply force_degree m _ (gaps (m-1) 0 0 1 0 0) h
        · apply gaps_nonzero; omega
        · intro i j
          fin_cases i <;> fin_cases j <;> simp [gaps] <;> omega
        · rw [gaps_weight]
          simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_sub hm₁]
          ring
        · rw [gaps_degree]; omega
    · have hbpos : 0 < b := by omega
      have hB : B = 0 := hb.resolve_left hbz
      subst B
      have hC : 1 ≤ C := by nlinarith
      apply force_degree m _ (gaps 1 0 1 0 0 1) h
      · apply gaps_nonzero; omega
      · intro i j
        fin_cases i <;> fin_cases j <;> simp [gaps] <;> omega
      · rw [gaps_weight]; norm_num
      · rw [gaps_degree]; omega

private theorem weight_transpose (m : ℕ) (alpha : Exponent) :
    weight m (Matrix.transpose alpha) = -weight m alpha := by
  unfold weight
  rw [Finset.sum_comm]
  simp only [Matrix.transpose_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem degree_transpose (alpha : Exponent) :
    degree (Matrix.transpose alpha) = degree alpha := by
  exact Finset.sum_comm

private theorem indecomposable_transpose (m : ℕ) (alpha : Exponent)
    (h : Indecomposable m alpha) : Indecomposable m (Matrix.transpose alpha) := by
  refine ⟨?_, ?_, ?_⟩
  · intro he
    apply h.1
    simpa using congrArg Matrix.transpose he
  · rw [weight_transpose, h.2.1, neg_zero]
  · intro beta hle hw
    have hle' : ∀ i j, beta j i ≤ alpha i j := fun i j => hle j i
    have hw' : weight m (Matrix.transpose beta) = 0 := by rw [weight_transpose, hw, neg_zero]
    rcases h.2.2 (fun i j => beta j i) hle' hw' with hz | he
    · left
      ext i j
      exact congrFun (congrFun hz j) i
    · right
      ext i j
      exact congrFun (congrFun he j) i

/-- Every indecomposable labelled zero-weight exponent has degree at most
2m minus one. Zero-weight units and distinct coordinates with coincident
numerical gaps are included, in particular at m equal to two. -/
theorem indecomposable_degree_bound (m : ℕ) (hm : 2 ≤ m) (alpha : Exponent)
    (h : Indecomposable m alpha) : degree alpha ≤ 2 * m - 1 := by
  classical
  by_cases hd : ∃ i, alpha i i ≠ 0
  · obtain ⟨i, hi⟩ := hd
    let beta := tensorExponent 1 i i
    have hb := tensor_monomial_bridge m 1 rho i i
    apply force_degree m alpha beta h
    · intro hz
      have he := congrArg (fun a : Exponent => a i i) hz
      simp [beta, tensorExponent, coordinateExponent] at he
    · intro a b
      change coordinateExponent i i a b ≤ alpha a b
      simp only [coordinateExponent]
      split_ifs with he
      · obtain ⟨rfl, rfl⟩ := he; omega
      · exact Nat.zero_le _
    · simpa [totalEnergy] using hb.2.1
    · rw [hb.1]; omega
  · have hz : ∀ i, alpha i i = 0 := by simpa using hd
    by_cases hp : ∃ i j, i ≠ j ∧ alpha i j ≠ 0 ∧ alpha j i ≠ 0
    · obtain ⟨i,j,hij,hi,hj⟩ := hp
      let beta := tensorExponent 2 (i,j) (j,i)
      have hb := tensor_monomial_bridge m 2 rho (i,j) (j,i)
      apply force_degree m alpha beta h
      · intro he
        have he' := congrArg (fun a : Exponent => a i j) he
        simp [beta, tensorExponent, coordinateExponent, hij, Ne.symm hij] at he'
      · intro a b
        change coordinateExponent i j a b + coordinateExponent j i a b ≤ alpha a b
        by_cases h₁ : a=i ∧ b=j
        · obtain ⟨rfl,rfl⟩ := h₁
          simp [coordinateExponent, hij, Ne.symm hij]; omega
        · by_cases h₂ : a=j ∧ b=i
          · obtain ⟨rfl,rfl⟩ := h₂
            simp [coordinateExponent, hij, Ne.symm hij]; omega
          · simp [coordinateExponent, h₁, h₂]
      · simpa [totalEnergy, add_comm] using hb.2.1
      · rw [hb.1]; omega
    · have hp' : ∀ i j, i ≠ j → alpha i j = 0 ∨ alpha j i = 0 := by
        intro i j hij
        by_contra! he
        exact hp ⟨i,j,hij,he.1,he.2⟩
      have oriented (a : Exponent) (ha : Indecomposable m a)
          (hz : ∀ i, a i i = 0) (h₁ : a 1 0 = 0 ∨ a 0 1 = 0)
          (h₂ : a 2 1 = 0 ∨ a 1 2 = 0) (h₃ : a 2 0 = 0) :
          degree a ≤ 2 * m - 1 := by
        have he : a = gaps (a 1 0) (a 0 1) (a 2 1) (a 1 2) 0 (a 0 2) := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [gaps, hz, h₃]
        rw [he] at ha ⊢
        apply oriented_bound m hm _ _ _ _ _ ha
        · simpa [gaps] using h₁
        · simpa [gaps] using h₂
      by_cases hmax : alpha 2 0 = 0
      · exact oriented alpha h hz (hp' 1 0 (by decide)) (hp' 2 1 (by decide)) hmax
      · rw [← degree_transpose alpha]
        apply oriented (Matrix.transpose alpha) (indecomposable_transpose m alpha h)
        · exact hz
        · exact (hp' 1 0 (by decide)).symm
        · exact (hp' 2 1 (by decide)).symm
        · exact (hp' 2 0 (by decide)).resolve_left hmax

#print axioms indecomposable_degree_bound
end D5.S3.Quantum.Fibers.SharedEnergyGapBound
