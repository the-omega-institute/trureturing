/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Actual ordered APPT spectra obey the uniform Schmidt variance bound at every physical rank at least two. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtBell

/-!
proof_shape: literal_r2_variance_moment: content
escape_witness: three actual bottom-slot cycles consume the singular-safe
  trace and sign row inequalities; the top pool is proved singleton.
proof_shape: literal_variance_moment: content
escape_witness: transport the actual complete-graph incidences into the
  pinned Fin-indexed assignment engine, discharge cardinalities and means,
  and consume the separate physical r=2 branch.
Every private helper below is consumed by these two statements. No supplied
PSD family, row identity, mean identity or target moment is a physical premise.
This is a necessary moment bridge, not a maximum-purity or attainment result.
-/

set_option autoImplicit false
open Matrix Finset
open scoped ComplexOrder BigOperators

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtVarianceConsumer
open UniformSchmidtCorner UniformSchmidtIncidence UniformSchmidtSpectrum
open UniformSchmidtBell UniformSchmidtDefectMoment QutritPerturbationAttainment
noncomputable section

/-- Positivity of the actual bottom-slot cardinality on the whole domain. -/
theorem bottom_pos {r : ℕ} (hr : 2 ≤ r) : 0 < b r := by
  have hb : b r = r + a r := by
    simp only [b, a, BottomSlot, Fintype.card_sum, Fintype.card_fin]
  omega

/-- Unnormalized centered variance, including singleton and zero pools. -/
def variance {k : ℕ} (z : Fin k → ℝ) : ℝ :=
  ∑ i, (z i - (∑ j, z j) / (k : ℝ))^2

/-- The two ACTUAL disjoint spectral pools, weighted as in the moment bound. -/
def momentLHS {r N : ℕ} (hN : a r + b r ≤ N) (l : Fin N → ℝ) : ℝ :=
  (((r : ℝ) - 1) / ((r : ℝ) + 1)) * variance (fun k => l (topIndex hN k)) +
    variance (fun k => l (bottomIndex hN k))

/-- The actual defect s=B-A and bottom-start eigenvalue cap. -/
def momentRHS {r N : ℕ} (hN : a r + b r ≤ N) (hb : 0 < b r)
    (l : Fin N → ℝ) : ℝ :=
  let B := ∑ k : Fin (b r), l (bottomIndex hN k)
  let A := ∑ k : Fin (a r), l (topIndex hN k)
  let s := B - A
  4 * s * min (B / ((r : ℝ) + 1)) (l (bottomStart hN hb)) -
    2 * s^2 / (r : ℝ)

private def finTopWeight {r : ℕ} (i : Fin r) (k : Fin (a r)) : ℝ :=
  topWeight i ((Fintype.equivFin (Edge r)).symm k)
private def finBottomWeight {r : ℕ} (i : Fin r) (k : Fin (b r)) : ℝ :=
  bottomWeight i ((Fintype.equivFin (BottomSlot r)).symm k)
private def finDiagSlot {r : ℕ} (i : Fin r) : Fin (b r) :=
  Fintype.equivFin (BottomSlot r) (.inl i)

private theorem sum_to_fin {α : Type*} [Fintype α] (f : α → ℝ) :
    (∑ k : Fin (Fintype.card α), f ((Fintype.equivFin α).symm k)) = ∑ x, f x :=
  (Fintype.equivFin α).symm.sum_comp f

private theorem top_fin_sum {r : ℕ} (i : Fin r) :
    (∑ k, finTopWeight i k) = -((r : ℝ) - 1) := by
  unfold finTopWeight
  rw [sum_to_fin, top_weight_sum]
private theorem top_fin_squares {r : ℕ} (i : Fin r) :
    (∑ k, (finTopWeight i k)^2) = (r : ℝ) - 1 := by
  change (∑ k, (fun e : Edge r => (topWeight i e)^2)
    ((Fintype.equivFin (Edge r)).symm k)) = _
  exact (sum_to_fin (fun e : Edge r => (topWeight i e)^2)).trans
    (top_weight_squares i)
private theorem bottom_fin_sum {r : ℕ} (i : Fin r) :
    (∑ k, finBottomWeight i k) = (r : ℝ) + 1 := by
  unfold finBottomWeight
  rw [sum_to_fin, bottom_weight_sum]
private theorem bottom_fin_squares {r : ℕ} (i : Fin r) :
    (∑ k, (finBottomWeight i k)^2) = (r : ℝ) + 3 := by
  change (∑ k, (fun p : BottomSlot r => (bottomWeight i p)^2)
    ((Fintype.equivFin (BottomSlot r)).symm k)) = _
  exact (sum_to_fin (fun p : BottomSlot r => (bottomWeight i p)^2)).trans
    (bottom_weight_squares i)

private theorem assigned_row_fin {r N : ℕ} (hN : a r + b r ≤ N)
    (l : Fin N → ℝ) (π : Equiv.Perm (Fin (a r)))
    (σ : Equiv.Perm (Fin (b r))) (i : Fin r) :
    rowSum (assignedK hN l π σ) i =
      (∑ k, finTopWeight i k * l (topIndex hN (π k))) +
      (∑ k, finBottomWeight i k * l (bottomIndex hN (σ k))) := by
  unfold assignedK
  rw [K_row]
  congr 1
  · simpa only [finTopWeight, Equiv.symm_apply_apply, assignedTopIndex] using
      (Fintype.equivFin (Edge r)).sum_comp
        (fun k => finTopWeight i k * l (topIndex hN (π k)))
  · simpa only [finBottomWeight, Equiv.symm_apply_apply, assignedBottomIndex] using
      (Fintype.equivFin (BottomSlot r)).sum_comp
        (fun k => finBottomWeight i k * l (bottomIndex hN (σ k)))

private theorem assigned_trace_fin {r N : ℕ} (hN : a r + b r ≤ N)
    (l : Fin N → ℝ) (π : Equiv.Perm (Fin (a r)))
    (σ : Equiv.Perm (Fin (b r))) :
    (assignedK hN l π σ).trace =
      2 * ∑ i, l (bottomIndex hN (σ (finDiagSlot i))) := by
  unfold assignedK
  rw [K_trace]
  rfl

private theorem pool_mean {r : ℕ} (hr : 3 ≤ r) (A B : ℝ) :
    -((r : ℝ) - 1) * (A / (a r : ℝ)) +
      ((r : ℝ) + 1) * (B / (b r : ℝ)) = 2 * (B - A) / (r : ℝ) := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (r : ℝ) ≠ 0 := by linarith
  have hrm : (r : ℝ) - 1 ≠ 0 := by linarith
  have hrp : (r : ℝ) + 1 ≠ 0 := by linarith
  change -((r : ℝ) - 1) * (A / (Fintype.card (Edge r) : ℝ)) +
    ((r : ℝ) + 1) * (B / (Fintype.card (BottomSlot r) : ℝ)) = _
  rw [edge_card_real, bottom_card_real]
  field_simp [hr0, hrm, hrp] <;> ring

private theorem literal_ge_three_variance_moment {r m n : ℕ} (hr : 3 ≤ r)
    (hm : r ≤ m) (hn : r ≤ n)
    (e : (Fin m × Fin n) ≃ Fin (m * n)) (l : Fin (m * n) → ℝ)
    (hl : Antitone l) (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) :
    let hN : a r + b r ≤ m * n :=
      (pool_card_sum r).trans_le (Nat.mul_le_mul hm hn)
    momentLHS hN l ≤ momentRHS hN (bottom_pos (by omega)) l := by
  dsimp only
  let hN : a r + b r ≤ m * n :=
    (pool_card_sum r).trans_le (Nat.mul_le_mul hm hn)
  have hac : (a r : ℝ) = (r : ℝ) * ((r : ℝ) - 1) / 2 := edge_card_real r
  have hbc : (b r : ℝ) = (r : ℝ) * ((r : ℝ) + 1) / 2 := bottom_card_real r
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have haR : (2 : ℝ) ≤ a r := by rw [hac]; nlinarith [sq_nonneg ((r : ℝ) - 3)]
  have hbR : (2 : ℝ) ≤ b r := by rw [hbc]; nlinarith [sq_nonneg ((r : ℝ) - 3)]
  have ha2 : 2 ≤ a r := by exact_mod_cast haR
  have hb2 : 2 ≤ b r := by exact_mod_cast hbR
  have hA : 0 < (a r : ℝ) := by linarith
  have hB : 0 < (b r : ℝ) := by linarith
  have ha1 : (a r : ℝ) - 1 ≠ 0 := by linarith
  have hb1 : (b r : ℝ) - 1 ≠ 0 := by linarith
  have htFactor (i : Fin r) :
      ((a r : ℝ) * ∑ k, (finTopWeight i k)^2 - (∑ k, finTopWeight i k)^2) /
          ((a r : ℝ) * ((a r : ℝ) - 1)) =
        2 * ((r : ℝ) - 1) / ((r : ℝ) * ((r : ℝ) + 1)) := by
    rw [top_fin_squares, top_fin_sum]
    exact (incidence_factors hr).1
  have hbFactor (i : Fin r) :
      ((b r : ℝ) * ∑ k, (finBottomWeight i k)^2 - (∑ k, finBottomWeight i k)^2) /
          ((b r : ℝ) * ((b r : ℝ) - 1)) = 2 / (r : ℝ) := by
    rw [bottom_fin_squares, bottom_fin_sum]
    exact (incidence_factors hr).2
  exact general_r_assignment_moment hr ha2 hb2
    (fun k => l (topIndex hN k)) (fun k => l (bottomIndex hN k))
    (assignedK hN l) finTopWeight finBottomWeight finDiagSlot
    ((∑ k : Fin (b r), l (bottomIndex hN k)) -
      ∑ k : Fin (a r), l (topIndex hN k))
    (l (bottomStart hN (bottom_pos (by omega))))
    hac hbc hA hB ha1 hb1 htFactor hbFactor top_fin_sum bottom_fin_sum
    (assigned_row_fin hN l) (assignedK_charge hN l) (assigned_trace_fin hN l)
    (fun π σ => literal_assignment_psd hm hn e l h π σ)
    (assignedK_offDiag hN l hl)
    (assignedK_diag hN (bottom_pos (by omega)) l hl)
    rfl (pool_mean hr _ _)

/- The singleton branch uses three genuine assignments of this SAME spectrum.
   It does not invoke the top permutation second moment at cardinality one. -/
private def edgeTwo : Edge 2 := ⟨(0, 1), by decide⟩
private theorem edge_two_unique (z : Edge 2) : z = edgeTwo := by
  rcases z with ⟨⟨i, j⟩, hij⟩
  change i.val < j.val at hij
  have hi : i = 0 := Fin.ext (by omega)
  have hj : j = 1 := Fin.ext (by omega)
  subst i
  subst j
  rfl

private theorem sum_edge_two (f : Edge 2 → ℝ) : ∑ z, f z = f edgeTwo := by
  classical
  have hu : (univ : Finset (Edge 2)) = {edgeTwo} := by
    ext z
    simp [edge_two_unique z]
  rw [hu, sum_singleton]

private theorem a_two_real : (a 2 : ℝ) = 1 := by
  change (Fintype.card (Edge 2) : ℝ) = 1
  norm_num [edge_card_real]
private theorem b_two_real : (b 2 : ℝ) = 3 := by
  change (Fintype.card (BottomSlot 2) : ℝ) = 3
  calc
    _ = (2 : ℝ) * (2 + 1) / 2 := bottom_card_real 2
    _ = 3 := by norm_num

private def cycleTwo : Equiv.Perm (BottomSlot 2) :=
  (Equiv.swap (.inl 0) (.inl 1)).trans (Equiv.swap (.inl 0) (.inr edgeTwo))
private def slotPermTwo (δ : Equiv.Perm (BottomSlot 2)) : Equiv.Perm (Fin (b 2)) :=
  (Fintype.equivFin (BottomSlot 2)).symm.trans
    (δ.trans (Fintype.equivFin (BottomSlot 2)))

private def twoMatrix (t u v w : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then (if i = 0 then 2 * u else 2 * v) else w - t
private theorem two_charge (t u v w : ℝ) :
    uniformCharge (twoMatrix t u v w) = 2 * (u + v + w - t) := by
  simp [uniformCharge, rowSum, twoMatrix, Fin.sum_univ_two]
  ring
private theorem two_trace (t u v w : ℝ) :
    (twoMatrix t u v w).trace = 2 * (u + v) := by
  simp [Matrix.trace, Matrix.diag_apply, twoMatrix, Fin.sum_univ_two]
  ring
private theorem two_energy (t u v w : ℝ) :
    centeredRowEnergy (twoMatrix t u v w) = 2 * (u - v)^2 := by
  simp [centeredRowEnergy, uniformCharge, rowSum, twoMatrix, Fin.sum_univ_two]
  ring
private theorem two_off (t u v w : ℝ) (hw : w ≤ t) :
    ∀ i j, i ≠ j → twoMatrix t u v w i j ≤ 0 := by
  intro i j hij
  simpa only [twoMatrix, if_neg hij, sub_nonpos] using hw
private theorem two_diag (t u v w γ : ℝ) (hu : u ≤ γ) (hv : v ≤ γ) :
    ∀ i, twoMatrix t u v w i i ≤ 2 * γ := by
  intro i
  fin_cases i
  · simpa [twoMatrix] using
      (mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 2))
  · simpa [twoMatrix] using
      (mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 2))

private theorem three_cycle_moment (t u v w γ : ℝ)
    (h0 : (twoMatrix t u v w).PosSemidef)
    (h1 : (twoMatrix t v w u).PosSemidef)
    (h2 : (twoMatrix t w u v).PosSemidef)
    (hut : u ≤ t) (hvt : v ≤ t) (hwt : w ≤ t)
    (huγ : u ≤ γ) (hvγ : v ≤ γ) (hwγ : w ≤ γ) :
    let B := u + v + w
    let s := B - t
    (u - B / 3)^2 + (v - B / 3)^2 + (w - B / 3)^2 ≤
      4 * s * min (B / 3) γ - s^2 := by
  dsimp only
  have ht0 := centered_row_moment (twoMatrix t u v w) h0
  have ht1 := centered_row_moment (twoMatrix t v w u) h1
  have ht2 := centered_row_moment (twoMatrix t w u v) h2
  have hg0 := centered_row_moment_of_nonpositive_offDiag
    (twoMatrix t u v w) h0 γ (two_off t u v w hwt) (two_diag t u v w γ huγ hvγ)
  have hg1 := centered_row_moment_of_nonpositive_offDiag
    (twoMatrix t v w u) h1 γ (two_off t v w u hut) (two_diag t v w u γ hvγ hwγ)
  have hg2 := centered_row_moment_of_nonpositive_offDiag
    (twoMatrix t w u v) h2 γ (two_off t w u v hvt) (two_diag t w u v γ hwγ huγ)
  simp only [two_energy, two_charge, two_trace, Fintype.card_fin] at ht0 ht1 ht2 hg0 hg1 hg2
  have htrace : (u - (u + v + w) / 3)^2 + (v - (u + v + w) / 3)^2 +
      (w - (u + v + w) / 3)^2 ≤
      4 * (u + v + w - t) * ((u + v + w) / 3) - (u + v + w - t)^2 := by
    nlinarith only [ht0, ht1, ht2]
  have hgamma : (u - (u + v + w) / 3)^2 + (v - (u + v + w) / 3)^2 +
      (w - (u + v + w) / 3)^2 ≤
      4 * (u + v + w - t) * γ - (u + v + w - t)^2 := by
    nlinarith only [hg0, hg1, hg2]
  by_cases hmin : (u + v + w) / 3 ≤ γ
  · rw [min_eq_left hmin]
    exact htrace
  · rw [min_eq_right (le_of_not_ge hmin)]
    exact hgamma

/-- The singleton top branch is consumed by `literal_variance_moment` below.
All three cyclic matrices are derived from literal APPT of the actual diagonal. -/
theorem literal_r2_variance_moment {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (e : (Fin m × Fin n) ≃ Fin (m * n)) (l : Fin (m * n) → ℝ)
    (hl : Antitone l) (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) :
    let hN : a 2 + b 2 ≤ m * n :=
      (pool_card_sum 2).trans_le (Nat.mul_le_mul hm hn)
    momentLHS hN l ≤ momentRHS hN (bottom_pos (by norm_num)) l := by
  classical
  dsimp only
  let hN : a 2 + b 2 ≤ m * n :=
    (pool_card_sum 2).trans_le (Nat.mul_le_mul hm hn)
  let T : Edge 2 → ℝ := fun z => l (topIndex hN (Fintype.equivFin (Edge 2) z))
  let Z : BottomSlot 2 → ℝ := fun p =>
    l (bottomIndex hN (Fintype.equivFin (BottomSlot 2) p))
  let t := T edgeTwo
  let u := Z (.inl 0)
  let v := Z (.inl 1)
  let w := Z (.inr edgeTwo)
  let γ := l (bottomStart hN (bottom_pos (by norm_num)))
  have hassign (δ : Equiv.Perm (BottomSlot 2)) :
      assignedK hN l (Equiv.refl _) (slotPermTwo δ) =
        K T (fun p => Z (δ p)) := by
    ext i j
    simp [assignedK, assignedTopIndex, assignedBottomIndex, slotPermTwo, T, Z]
  have hmatrix0 : assignedK hN l (Equiv.refl _) (slotPermTwo (Equiv.refl _)) =
      twoMatrix t u v w := by
    rw [hassign]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [K, twoMatrix, edge, edgeTwo, t, u, v, w]
  have hmatrix1 : assignedK hN l (Equiv.refl _) (slotPermTwo cycleTwo) =
      twoMatrix t v w u := by
    rw [hassign]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [K, twoMatrix, edge, edgeTwo, cycleTwo, Equiv.swap_apply_def, t, u, v, w]
  have hmatrix2 : assignedK hN l (Equiv.refl _) (slotPermTwo (cycleTwo.trans cycleTwo)) =
      twoMatrix t w u v := by
    rw [hassign]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [K, twoMatrix, edge, edgeTwo, cycleTwo, Equiv.swap_apply_def, t, u, v, w]
  have h0 : (twoMatrix t u v w).PosSemidef := by
    rw [← hmatrix0]
    exact literal_assignment_psd hm hn e l h _ _
  have h1 : (twoMatrix t v w u).PosSemidef := by
    rw [← hmatrix1]
    exact literal_assignment_psd hm hn e l h _ _
  have h2 : (twoMatrix t w u v).PosSemidef := by
    rw [← hmatrix2]
    exact literal_assignment_psd hm hn e l h _ _
  have hsep (p : BottomSlot 2) : Z p ≤ t :=
    hl (le_of_lt (bottom_top_separated hN
      (Fintype.equivFin (Edge 2) edgeTwo) (Fintype.equivFin (BottomSlot 2) p)))
  have hcap (p : BottomSlot 2) : Z p ≤ γ := by
    apply hl
    change m * n - b 2 ≤ m * n - b 2 + (Fintype.equivFin (BottomSlot 2) p).val
    omega
  have hbnd := three_cycle_moment t u v w γ h0 h1 h2
    (hsep (.inl 0)) (hsep (.inl 1)) (hsep (.inr edgeTwo))
    (hcap (.inl 0)) (hcap (.inl 1)) (hcap (.inr edgeTwo))
  have hA : (∑ k : Fin (a 2), l (topIndex hN k)) = t := by
    rw [← (Fintype.equivFin (Edge 2)).sum_comp (fun k => l (topIndex hN k))]
    exact sum_edge_two T
  have hB : (∑ k : Fin (b 2), l (bottomIndex hN k)) = u + v + w := by
    rw [← (Fintype.equivFin (BottomSlot 2)).sum_comp (fun k => l (bottomIndex hN k))]
    change (∑ p : BottomSlot 2, Z p) = _
    rw [Fintype.sum_sum_type, Fin.sum_univ_two, sum_edge_two]
  have hVT : variance (fun k : Fin (a 2) => l (topIndex hN k)) = 0 := by
    unfold variance
    rw [hA, a_two_real]
    rw [← (Fintype.equivFin (Edge 2)).sum_comp
      (fun k => (l (topIndex hN k) - t / 1)^2)]
    rw [sum_edge_two]
    simp [t, T]
  have hVB : variance (fun k : Fin (b 2) => l (bottomIndex hN k)) =
      (u - (u + v + w) / 3)^2 + (v - (u + v + w) / 3)^2 +
        (w - (u + v + w) / 3)^2 := by
    unfold variance
    rw [hB, b_two_real]
    rw [← (Fintype.equivFin (BottomSlot 2)).sum_comp
      (fun k => (l (bottomIndex hN k) - (u + v + w) / 3)^2)]
    rw [Fintype.sum_sum_type, Fin.sum_univ_two, sum_edge_two]
  dsimp only [momentLHS, momentRHS]
  rw [hVT, hVB, hA, hB]
  dsimp only at hbnd
  convert hbnd using 1 <;> norm_num [γ] <;> ring

/-- Full physical domain. Ties, zero eigenvalues, zero defect, and singular PSD
are retained. The only physical premise is literal APPT of THIS diagonal. -/
theorem literal_variance_moment {r m n : ℕ} (hr : 2 ≤ r)
    (hm : r ≤ m) (hn : r ≤ n)
    (e : (Fin m × Fin n) ≃ Fin (m * n)) (l : Fin (m * n) → ℝ)
    (hl : Antitone l) (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) :
    let hN : a r + b r ≤ m * n :=
      (pool_card_sum r).trans_le (Nat.mul_le_mul hm hn)
    momentLHS hN l ≤ momentRHS hN (bottom_pos hr) l := by
  by_cases hr2 : r = 2
  · subst r
    exact literal_r2_variance_moment hm hn e l hl h
  · exact literal_ge_three_variance_moment (by omega) hm hn e l hl h

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtVarianceConsumer
