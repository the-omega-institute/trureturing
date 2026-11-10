/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/UniformSchmidtHeadCap
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/UniformSchmidtHeadCap
   mirror-E: none(waiver:symbolic-spectral-inequality)
   anchors: []
   utility: none
   digest: Literal APPT forces a homogeneous rank-six head cap by a nonnegative test vector. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtBell

/-! A necessary spectral head bound obtained from an actual Bell assignment. -/

set_option autoImplicit false
open Matrix Finset
open scoped ComplexOrder BigOperators

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.UniformSchmidtHeadCap
open UniformSchmidtIncidence UniformSchmidtSpectrum UniformSchmidtBell
open QutritPerturbationAttainment
noncomputable section

/- All helpers are consumed by the literal spectral conclusion. The finite
six-coordinate computation evaluates a symbolic quadratic form, not a
certificate for one spectrum. The spectral conclusion ranges over every
ambient pair m,n >= 6 and allows ties, zero eigenvalues and singular PSD. -/

private theorem six_top_card : a 6 = 15 := by
  have h := edge_card_real 6
  norm_num at h
  exact_mod_cast h

private theorem six_bottom_card : b 6 = 21 := by
  have h := bottom_card_real 6
  norm_num at h
  exact_mod_cast h

private theorem quadratic_mono_nonneg {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) (hAB : ∀ i j, A i j ≤ B i j)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x) := by
  apply dotProduct_le_dotProduct_of_nonneg_left _ hx
  intro i
  exact dotProduct_le_dotProduct_of_nonneg_right (hAB i) hx

private def model (u v L : ℝ) : Matrix (Fin 6) (Fin 6) ℝ := fun i j =>
  if i = j then 2 * u
  else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then u - L else -v

private def test (p q : ℝ) : Fin 6 → ℝ := fun i => if i < 2 then p else q

private theorem model_quadratic (u v L p q : ℝ) :
    test p q ⬝ᵥ (model u v L *ᵥ test p q) =
      2 * ((3 * u - L) * p^2 - 8 * v * p * q + (4 * u - 6 * v) * q^2) := by
  norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, model, test]
  ring

private theorem matrix_head_cap (A : Matrix (Fin 6) (Fin 6) ℝ)
    (hA : A.PosSemidef) (u v L : ℝ) (hu : 0 < u) (hv : 0 ≤ v)
    (hd : ∀ i, A i i ≤ 2 * u)
    (ho : ∀ i j, i ≠ j → A i j ≤ -v)
    (h01 : A 0 1 ≤ u - L) (h10 : A 1 0 ≤ u - L) :
    15 * v ≤ 6 * u ∧ (3 * u - L) * (2 * u - 3 * v) ≥ 8 * v^2 := by
  have hall : ∀ i j, A i j ≤ if i = j then 2 * u else -v := by
    intro i j
    split_ifs with hij
    · subst j; exact hd i
    · exact ho i j hij
  have hq := hA.dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
  have hc := quadratic_mono_nonneg A (fun i j => if i = j then 2 * u else -v)
    hall (fun _ => 1) (fun _ => by norm_num)
  have hsum : (fun _ : Fin 6 => (1 : ℝ)) ⬝ᵥ
      ((fun i j : Fin 6 => if i = j then 2 * u else -v) *ᵥ fun _ => 1) =
        12 * u - 30 * v := by
    norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
    <;> ring
  rw [hsum] at hc
  have hnonneg : 0 ≤ 12 * u - 30 * v := le_trans hq hc
  have hratio : 15 * v ≤ 6 * u := by linarith
  have hp : 0 < 2 * u - 3 * v := by linarith
  have hmodel : ∀ i j, A i j ≤ model u v L i j := by
    intro i j
    unfold model
    split_ifs with hij hspecial
    · subst j; exact hd i
    · rcases hspecial with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h01
      · exact h10
    · exact ho i j hij
  have hx : ∀ i, 0 ≤ test (2 * u - 3 * v) (2 * v) i := by
    intro i
    unfold test
    split_ifs <;> linarith
  have hactual := hA.dotProduct_mulVec_nonneg (test (2 * u - 3 * v) (2 * v))
  have hcompare := quadratic_mono_nonneg A (model u v L) hmodel
    (test (2 * u - 3 * v) (2 * v)) hx
  rw [model_quadratic] at hcompare
  have hfactor : 0 ≤ (2 * u - 3 * v) *
      ((3 * u - L) * (2 * u - 3 * v) - 8 * v^2) := by
    nlinarith only [le_trans hactual hcompare]
  exact ⟨hratio, by linarith only [(nonneg_of_mul_nonneg_right hfactor hp)]⟩

/-- A necessary head bound for an actual normalized, sorted APPT spectrum.
Here u is the largest of the last 21 entries, u+v is the smallest of the
first 15, and L is the largest entry. No strict positivity is assumed.
The conclusion is neither APPT sufficiency nor a purity maximization. -/
theorem literal_rank_six_head_cap {m n : ℕ} (hm : 6 ≤ m) (hn : 6 ≤ n)
    (e : (Fin m × Fin n) ≃ Fin (m * n)) (l : Fin (m * n) → ℝ)
    (hl : Antitone l) (hl0 : ∀ i, 0 ≤ l i) (hmass : ∑ i, l i = 1)
    (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) :
    let hN : a 6 + b 6 ≤ m * n :=
      (pool_card_sum 6).trans_le (Nat.mul_le_mul hm hn)
    let u := l (bottomStart hN (by rw [six_bottom_card]; omega))
    let v := l (topIndex hN ⟨14, by rw [six_top_card]; omega⟩) - u
    let L := l (topIndex hN ⟨0, by rw [six_top_card]; omega⟩)
    0 < u ∧ 0 ≤ v ∧ 15 * v ≤ 6 * u ∧ 0 ≤ L - u - v ∧
      8 * v^2 ≤ (3 * u - L) * (2 * u - 3 * v) ∧
      L - u - v ≤ 2 * u - v - 8 * v^2 / (2 * u - 3 * v) := by
  classical
  dsimp only
  let hN : a 6 + b 6 ≤ m * n :=
    (pool_card_sum 6).trans_le (Nat.mul_le_mul hm hn)
  have hb : 0 < b 6 := by rw [six_bottom_card]; omega
  let k0 : Fin (a 6) := ⟨0, by rw [six_top_card]; omega⟩
  let klast : Fin (a 6) := ⟨14, by rw [six_top_card]; omega⟩
  let u := l (bottomStart hN hb)
  let v := l (topIndex hN klast) - u
  let L := l (topIndex hN k0)
  change 0 < u ∧ 0 ≤ v ∧ 15 * v ≤ 6 * u ∧ 0 ≤ L - u - v ∧
    8 * v^2 ≤ (3 * u - L) * (2 * u - 3 * v) ∧
    L - u - v ≤ 2 * u - v - 8 * v^2 / (2 * u - 3 * v)
  have hbottom (k : Fin (b 6)) : l (bottomIndex hN k) ≤ u := by
    apply hl
    change m * n - b 6 ≤ m * n - b 6 + k.val
    omega
  have htop (k : Fin (a 6)) : u + v ≤ l (topIndex hN k) := by
    have hle : topIndex hN k ≤ topIndex hN klast := by
      change k.val ≤ 14
      have := k.isLt
      have ha := six_top_card
      omega
    dsimp [v]
    linarith [hl hle]
  have hv : 0 ≤ v := by
    have hs := hl (le_of_lt (bottom_top_separated hN klast ⟨0, hb⟩))
    have heq : bottomIndex hN ⟨0, hb⟩ = bottomStart hN hb := by
      apply Fin.ext
      simp [bottomIndex, bottomStart]
    rw [heq] at hs
    exact sub_nonneg.mpr hs
  let e01 : Edge 6 := edge 0 1 (by decide)
  let π : Equiv.Perm (Fin (a 6)) := Equiv.swap (Fintype.equivFin _ e01) k0
  let σ : Equiv.Perm (Fin (b 6)) := Equiv.refl _
  let A := assignedK hN l π σ
  have hA : A.PosSemidef := literal_assignment_psd hm hn e l h π σ
  have hcharge : 0 ≤ 2 * ((∑ k : Fin (b 6), l (bottomIndex hN k)) -
      ∑ k : Fin (a 6), l (topIndex hN k)) := by
    rw [← assignedK_charge hN l π σ]
    have hh := hA.dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
    simpa [A, UniformSchmidtDefectMoment.uniformCharge,
      UniformSchmidtDefectMoment.rowSum, dotProduct, Matrix.mulVec] using hh
  have hB : (∑ k : Fin (b 6), l (bottomIndex hN k)) ≤ 21 * u := by
    calc
      _ ≤ ∑ _ : Fin (b 6), u := sum_le_sum (fun k _ => hbottom k)
      _ = _ := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
          six_bottom_card]
        norm_num
  have hL : L ≤ ∑ k : Fin (a 6), l (topIndex hN k) := by
    exact single_le_sum (fun k _ => hl0 (topIndex hN k)) (mem_univ k0)
  have hu0 : 0 ≤ u := hl0 _
  have hu : 0 < u := by
    by_contra hu
    have huz : u = 0 := le_antisymm (le_of_not_gt hu) hu0
    have hLz : L ≤ 0 := by linarith
    have hz (i : Fin (m * n)) : l i ≤ 0 := by
      have hi : topIndex hN k0 ≤ i := by change 0 ≤ i.val; omega
      exact (hl hi).trans hLz
    have hsum : (∑ i, l i) ≤ 0 := sum_nonpos (fun i _ => hz i)
    linarith
  have hdiag (i : Fin 6) : A i i ≤ 2 * u := assignedK_diag hN hb l hl π σ i
  have hoff (i j : Fin 6) (hij : i ≠ j) : A i j ≤ -v := by
    change K _ _ i j ≤ -v
    rw [K, dite_eq_right hij]
    have hb' := hbottom (σ (Fintype.equivFin _ (.inr (edge i j hij))))
    have ht' := htop (π (Fintype.equivFin _ (edge i j hij)))
    change l (bottomIndex hN _) - l (topIndex hN _) ≤ -v
    linarith
  have hspecial : ∀ i j : Fin 6, (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) →
      A i j ≤ u - L := by
    intro i j hij
    have he : edge i j (by rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) = e01 := by
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [e01, edge]
    have hne : i ≠ j := by rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    change K _ _ i j ≤ u - L
    rw [K, dite_eq_right hne, he]
    have hb' := hbottom (σ (Fintype.equivFin _ (.inr e01)))
    have ht' : l (assignedTopIndex hN π e01) = L := by
      simp [assignedTopIndex, π, L]
    change l (assignedBottomIndex hN σ (.inr e01)) - l (assignedTopIndex hN π e01) ≤ _
    rw [ht']
    exact sub_le_sub_right hb' L
  obtain ⟨hratio, hcap⟩ := matrix_head_cap A hA u v L hu hv hdiag hoff
    (hspecial 0 1 (Or.inl ⟨rfl, rfl⟩)) (hspecial 1 0 (Or.inr ⟨rfl, rfl⟩))
  have hp : 0 < 2 * u - 3 * v := by linarith
  have hhead : 0 ≤ L - u - v := by
    have ht' := htop k0
    change u + v ≤ L at ht'
    linarith
  refine ⟨hu, hv, hratio, hhead, hcap, ?_⟩
  have hdiv : 8 * v^2 / (2 * u - 3 * v) ≤ 3 * u - L :=
    (div_le_iff₀ hp).mpr hcap
  linarith

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.UniformSchmidtHeadCap
