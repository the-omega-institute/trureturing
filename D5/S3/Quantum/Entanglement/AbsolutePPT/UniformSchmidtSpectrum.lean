/- Uncompiled source candidate. One actual spectrum, independent pool
   permutations, and a true injective labelling of its product corner.
   Generic Bell unitarity/compression and final moment integration remain
   as specified in LiteralSchmidtBridge.md; no final physical theorem is assumed. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtCorner
import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtIncidence

set_option autoImplicit false
open Matrix
open scoped ComplexOrder BigOperators

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtSpectrum
open UniformSchmidtCorner UniformSchmidtIncidence QutritPerturbationAttainment
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
noncomputable section

abbrev a (r : ℕ) := Fintype.card (Edge r)
abbrev b (r : ℕ) := Fintype.card (BottomSlot r)

def bellSlotsEquiv (r : ℕ) : (BottomSlot r ⊕ Edge r) ≃ (Fin r × Fin r) :=
  (Equiv.sumAssoc (Fin r) (Edge r) (Edge r)).trans (slotEquiv r)

theorem pool_card_sum (r : ℕ) : a r + b r = r * r := by
  have hc := Fintype.card_congr (bellSlotsEquiv r)
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at hc
  simp only [a, b, BottomSlot, Fintype.card_sum, Fintype.card_fin]
  omega

def topIndex {N a b : ℕ} (hN : a + b ≤ N) (i : Fin a) : Fin N :=
  ⟨i.val, by omega⟩

def bottomIndex {N a b : ℕ} (hN : a + b ≤ N) (i : Fin b) : Fin N :=
  ⟨N - b + i.val, by omega⟩

def bottomStart {N a b : ℕ} (hN : a + b ≤ N) (hb : 0 < b) : Fin N :=
  ⟨N - b, by omega⟩

theorem topIndex_injective {N a b : ℕ} (hN : a + b ≤ N) :
    Function.Injective (topIndex hN) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin N => z.val) h

theorem bottomIndex_injective {N a b : ℕ} (hN : a + b ≤ N) :
    Function.Injective (bottomIndex hN) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [bottomIndex] at this
  omega

theorem bottom_top_separated {N a b : ℕ} (hN : a + b ≤ N)
    (i : Fin a) (j : Fin b) : topIndex hN i < bottomIndex hN j := by
  change i.val < N - b + j.val
  omega

def assignedTopIndex {r N : ℕ} (hN : a r + b r ≤ N)
    (π : Equiv.Perm (Fin (a r))) (e : Edge r) : Fin N :=
  topIndex hN (π (Fintype.equivFin (Edge r) e))

def assignedBottomIndex {r N : ℕ} (hN : a r + b r ≤ N)
    (σ : Equiv.Perm (Fin (b r))) (p : BottomSlot r) : Fin N :=
  bottomIndex hN (σ (Fintype.equivFin (BottomSlot r) p))

def label {r N : ℕ} (hN : a r + b r ≤ N)
    (π : Equiv.Perm (Fin (a r))) (σ : Equiv.Perm (Fin (b r))) :
    Fin r × Fin r → Fin N :=
  (Sum.elim (assignedBottomIndex hN σ) (assignedTopIndex hN π)) ∘
    (bellSlotsEquiv r).symm

theorem label_injective {r N : ℕ} (hN : a r + b r ≤ N)
    (π : Equiv.Perm (Fin (a r))) (σ : Equiv.Perm (Fin (b r))) :
    Function.Injective (label hN π σ) := by
  have ht : Function.Injective (assignedTopIndex hN π) :=
    (topIndex_injective hN).comp (π.injective.comp (Fintype.equivFin _).injective)
  have hb : Function.Injective (assignedBottomIndex hN σ) :=
    (bottomIndex_injective hN).comp (σ.injective.comp (Fintype.equivFin _).injective)
  have hsplit : Function.Injective
      (Sum.elim (assignedBottomIndex hN σ) (assignedTopIndex hN π)) := by
    intro x y h
    rcases x with p | e <;> rcases y with q | f
    · exact congrArg Sum.inl (hb h)
    · have hlt := bottom_top_separated hN
        (π (Fintype.equivFin _ f)) (σ (Fintype.equivFin _ p))
      exact False.elim ((ne_of_lt hlt) h.symm)
    · have hlt := bottom_top_separated hN
        (π (Fintype.equivFin _ e)) (σ (Fintype.equivFin _ q))
      exact False.elim ((ne_of_lt hlt) h)
    · exact congrArg Sum.inr (ht h)
  exact hsplit.comp (bellSlotsEquiv r).symm.injective

def assignedK {r N : ℕ} (hN : a r + b r ≤ N) (l : Fin N → ℝ)
    (π : Equiv.Perm (Fin (a r))) (σ : Equiv.Perm (Fin (b r))) :
    Matrix (Fin r) (Fin r) ℝ :=
  K (fun e => l (assignedTopIndex hN π e))
    (fun p => l (assignedBottomIndex hN σ p))

theorem assignedK_offDiag {r N : ℕ} (hN : a r + b r ≤ N)
    (l : Fin N → ℝ) (hl : Antitone l)
    (π : Equiv.Perm (Fin (a r))) (σ : Equiv.Perm (Fin (b r)))
    (i j : Fin r) (hij : i ≠ j) : assignedK hN l π σ i j ≤ 0 := by
  apply K_offDiag _ _ _ i j hij
  intro e f
  exact hl (le_of_lt (bottom_top_separated hN
    (π (Fintype.equivFin _ f)) (σ (Fintype.equivFin _ (.inr e)))))

theorem assignedK_diag {r N : ℕ} (hN : a r + b r ≤ N) (hb : 0 < b r)
    (l : Fin N → ℝ) (hl : Antitone l)
    (π : Equiv.Perm (Fin (a r))) (σ : Equiv.Perm (Fin (b r))) (i : Fin r) :
    assignedK hN l π σ i i ≤ 2 * l (bottomStart hN hb) := by
  apply K_diag _ _ _ _ i
  intro j
  apply hl
  change N - b r ≤ N - b r + (σ (Fintype.equivFin _ (.inl j))).val
  omega

theorem sum_assignedTop {r N : ℕ} (hN : a r + b r ≤ N) (l : Fin N → ℝ)
    (π : Equiv.Perm (Fin (a r))) :
    (∑ e : Edge r, l (assignedTopIndex hN π e)) =
      ∑ k : Fin (a r), l (topIndex hN k) := by
  calc
    _ = ∑ k : Fin (a r), l (topIndex hN (π k)) :=
      (Fintype.equivFin (Edge r)).sum_comp (fun k => l (topIndex hN (π k)))
    _ = _ := Equiv.sum_comp π (fun k => l (topIndex hN k))

theorem sum_assignedBottom {r N : ℕ} (hN : a r + b r ≤ N) (l : Fin N → ℝ)
    (σ : Equiv.Perm (Fin (b r))) :
    (∑ p : BottomSlot r, l (assignedBottomIndex hN σ p)) =
      ∑ k : Fin (b r), l (bottomIndex hN k) := by
  calc
    _ = ∑ k : Fin (b r), l (bottomIndex hN (σ k)) :=
      (Fintype.equivFin (BottomSlot r)).sum_comp (fun k => l (bottomIndex hN (σ k)))
    _ = _ := Equiv.sum_comp σ (fun k => l (bottomIndex hN k))

theorem assignedK_charge {r N : ℕ} (hN : a r + b r ≤ N) (l : Fin N → ℝ)
    (π : Equiv.Perm (Fin (a r))) (σ : Equiv.Perm (Fin (b r))) :
    UniformSchmidtDefectMoment.uniformCharge (assignedK hN l π σ) =
      2 * ((∑ k : Fin (b r), l (bottomIndex hN k)) -
        ∑ k : Fin (a r), l (topIndex hN k)) := by
  unfold assignedK
  rw [K_charge, sum_assignedBottom, sum_assignedTop]

/-- The whole selected product corner is PSD after any genuine corner
unitary. Here label injectivity is PROVED from disjoint actual pool indices.
No normalization or distinctness of the spectrum's values is required. -/
theorem actual_corner_psd {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n)
    (e : (Fin m × Fin n) ≃ Fin (m * n)) (l : Fin (m * n) → ℝ)
    (h : APPT (diagonal (fun p => (l (e p) : ℂ))))
    (π : Equiv.Perm (Fin (a r))) (σ : Equiv.Perm (Fin (b r)))
    (V : unitaryGroup (Fin r × Fin r) ℂ) :
    let hN : a r + b r ≤ m * n :=
      (pool_card_sum r).trans_le (Nat.mul_le_mul hm hn)
    (partialTranspose ((V : Matrix _ _ ℂ) *
      diagonal (fun q => (l (label hN π σ q) : ℂ)) * (V : Matrix _ _ ℂ)ᴴ)).PosSemidef := by
  dsimp only
  exact selected_corner_psd hm hn e l _ (label_injective _ π σ) h V

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtSpectrum
