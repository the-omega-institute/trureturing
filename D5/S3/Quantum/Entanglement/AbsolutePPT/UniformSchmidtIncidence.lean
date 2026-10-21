/- Uncompiled source candidate. Actual complete-graph slots and incidence
   moments for the literal consumer in LiteralSchmidtBridge.md.
   This file supplies no replacement APPT predicate or assignment-PSD assumption. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment

set_option autoImplicit false
open Matrix Finset
open scoped BigOperators

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtIncidence
noncomputable section

abbrev Edge (r : ℕ) := {p : Fin r × Fin r // p.1 < p.2}
abbrev BottomSlot (r : ℕ) := Fin r ⊕ Edge r

def slotCoord {r : ℕ} : (Fin r ⊕ (Edge r ⊕ Edge r)) → Fin r × Fin r
  | .inl i => (i, i)
  | .inr (.inl e) => e.val
  | .inr (.inr e) => (e.val.2, e.val.1)

def coordSlot {r : ℕ} (p : Fin r × Fin r) : Fin r ⊕ (Edge r ⊕ Edge r) :=
  if h : p.1 = p.2 then .inl p.1
  else if hlt : p.1 < p.2 then .inr (.inl ⟨p, hlt⟩)
  else .inr (.inr ⟨(p.2, p.1), by change p.2 < p.1; omega⟩)

def slotEquiv (r : ℕ) : (Fin r ⊕ (Edge r ⊕ Edge r)) ≃ (Fin r × Fin r) where
  toFun := slotCoord
  invFun := coordSlot
  left_inv := by
    intro z
    rcases z with i | (e | e)
    · simp [slotCoord, coordSlot]
    · rcases e with ⟨⟨i, j⟩, hij⟩
      simp [slotCoord, coordSlot, ne_of_lt hij, hij]
    · rcases e with ⟨⟨i, j⟩, hij⟩
      simp [slotCoord, coordSlot, ne_of_gt hij, not_lt_of_gt hij]
  right_inv := by
    rintro ⟨i, j⟩
    simp only [coordSlot]
    split_ifs <;> simp_all [slotCoord]

theorem edge_card_real (r : ℕ) :
    (Fintype.card (Edge r) : ℝ) = (r : ℝ) * ((r : ℝ) - 1) / 2 := by
  have hc := Fintype.card_congr (slotEquiv r)
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod] at hc
  have hcR : (r : ℝ) + ((Fintype.card (Edge r) : ℝ) +
      (Fintype.card (Edge r) : ℝ)) = (r : ℝ) * (r : ℝ) := by exact_mod_cast hc
  nlinarith

theorem bottom_card_real (r : ℕ) :
    (Fintype.card (BottomSlot r) : ℝ) = (r : ℝ) * ((r : ℝ) + 1) / 2 := by
  simp only [BottomSlot, Fintype.card_sum, Fintype.card_fin, Nat.cast_add]
  rw [edge_card_real]
  ring

def incident {r : ℕ} (i : Fin r) (e : Edge r) : Prop :=
  i = e.val.1 ∨ i = e.val.2

instance incidentDecidable {r : ℕ} (i : Fin r) (e : Edge r) :
    Decidable (incident i e) :=
  inferInstanceAs (Decidable (i = e.val.1 ∨ i = e.val.2))

def edge {r : ℕ} (i j : Fin r) (h : i ≠ j) : Edge r :=
  if hij : i < j then ⟨(i, j), hij⟩ else ⟨(j, i), by change j < i; omega⟩

theorem edge_symm {r : ℕ} (i j : Fin r) (h : i ≠ j) :
    edge i j h = edge j i h.symm := by
  apply Subtype.ext
  simp only [edge]
  split_ifs <;> simp_all <;> omega

def incidentNeighbor {r : ℕ} (i : Fin r) (e : {e : Edge r // incident i e}) :
    {j : Fin r // j ≠ i} :=
  if h : i = e.val.val.1 then ⟨e.val.val.2, by have := e.val.property; omega⟩
  else ⟨e.val.val.1, Ne.symm h⟩

def neighborIncident {r : ℕ} (i : Fin r) (j : {j : Fin r // j ≠ i}) :
    {e : Edge r // incident i e} :=
  ⟨edge i j.val j.property.symm, by
    unfold edge incident
    split_ifs <;> simp⟩

def incidentEquiv {r : ℕ} (i : Fin r) :
    {e : Edge r // incident i e} ≃ {j : Fin r // j ≠ i} where
  toFun := incidentNeighbor i
  invFun := neighborIncident i
  left_inv := by
    rintro ⟨⟨⟨a, b⟩, hab⟩, hi⟩
    apply Subtype.ext
    apply Subtype.ext
    simp only [incident] at hi
    rcases hi with rfl | rfl
    · simp [incidentNeighbor, neighborIncident, edge, hab, ne_of_lt hab]
    · simp [incidentNeighbor, neighborIncident, edge, ne_of_gt hab, not_lt_of_gt hab]
  right_inv := by
    rintro ⟨j, hji⟩
    apply Subtype.ext
    by_cases hij : i < j
    · simp [neighborIncident, incidentNeighbor, edge, hij]
    · simp [neighborIncident, incidentNeighbor, edge, hij, Ne.symm hji]

theorem incident_card {r : ℕ} (i : Fin r) :
    Fintype.card {e : Edge r // incident i e} = r - 1 := by
  rw [Fintype.card_congr (incidentEquiv i)]
  simpa only [Fintype.card_fin, Fintype.card_subtype_eq] using
    (Fintype.card_subtype_compl (fun j : Fin r => j = i))

def topWeight {r : ℕ} (i : Fin r) (e : Edge r) : ℝ :=
  if incident i e then -1 else 0

def bottomWeight {r : ℕ} (i : Fin r) : BottomSlot r → ℝ
  | .inl j => if i = j then 2 else 0
  | .inr e => if incident i e then 1 else 0

theorem incident_indicator_sum {r : ℕ} (i : Fin r) :
    (∑ e : Edge r, if incident i e then (1 : ℝ) else 0) = (r : ℝ) - 1 := by
  classical
  have hr : 1 ≤ r := by have := i.isLt; omega
  have he : (∑ e : Edge r, if incident i e then (1 : ℝ) else 0) =
      (Fintype.card {e : Edge r // incident i e} : ℝ) := by
    simp [Finset.sum_ite, Fintype.card_subtype]
  rw [he, incident_card, Nat.cast_sub hr]
  norm_num

theorem top_weight_sum {r : ℕ} (i : Fin r) :
    (∑ e, topWeight i e) = -((r : ℝ) - 1) := by
  classical
  calc
    _ = -(∑ e : Edge r, if incident i e then (1 : ℝ) else 0) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro e _
      by_cases hi : incident i e <;> simp [topWeight, hi]
    _ = _ := by rw [incident_indicator_sum]

theorem top_weight_squares {r : ℕ} (i : Fin r) :
    (∑ e, (topWeight i e)^2) = (r : ℝ) - 1 := by
  classical
  calc
    _ = ∑ e : Edge r, if incident i e then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro e _
      by_cases hi : incident i e <;> simp [topWeight, hi]
    _ = _ := incident_indicator_sum i

theorem bottom_weight_sum {r : ℕ} (i : Fin r) :
    (∑ p, bottomWeight i p) = (r : ℝ) + 1 := by
  classical
  simp only [Fintype.sum_sum_type, bottomWeight]
  rw [Fintype.sum_ite_eq i (fun _ => (2 : ℝ)), incident_indicator_sum]
  ring

theorem bottom_weight_squares {r : ℕ} (i : Fin r) :
    (∑ p, (bottomWeight i p)^2) = (r : ℝ) + 3 := by
  classical
  have hd : (∑ j : Fin r, (if i = j then (2 : ℝ) else 0)^2) = 4 := by
    simp <;> norm_num
  have he : (∑ e : Edge r, (if incident i e then (1 : ℝ) else 0)^2) =
      (r : ℝ) - 1 := by simpa using incident_indicator_sum i
  simp only [Fintype.sum_sum_type, bottomWeight]
  rw [hd, he]
  ring

def K {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ) :
    Matrix (Fin r) (Fin r) ℝ := fun i j =>
  if h : i = j then 2 * b (.inl i)
  else b (.inr (edge i j h)) - t (edge i j h)

theorem K_isHermitian {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ) :
    (K t b).IsHermitian := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [K, Matrix.conjTranspose_apply]
  · simp only [K, Matrix.conjTranspose_apply, dif_neg h, dif_neg (Ne.symm h),
      star_sub, star_trivial]
    rw [edge_symm j i (Ne.symm h)]

theorem K_offDiag {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ)
    (hsep : ∀ e f, b (.inr e) ≤ t f) (i j : Fin r) (h : i ≠ j) :
    K t b i j ≤ 0 := by
  simpa [K, h, sub_nonpos] using hsep (edge i j h) (edge i j h)

theorem K_diag {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ)
    (γ : ℝ) (hb : ∀ i, b (.inl i) ≤ γ) (i : Fin r) : K t b i i ≤ 2 * γ := by
  simpa [K] using mul_le_mul_of_nonneg_left (hb i) (by norm_num : (0 : ℝ) ≤ 2)

theorem incident_sum {r : ℕ} (i : Fin r) (f : Edge r → ℝ) :
    (∑ j : {j : Fin r // j ≠ i}, f (edge i j.val j.property.symm)) =
      ∑ e : Edge r, if incident i e then f e else 0 := by
  classical
  calc
    _ = ∑ z : {e : Edge r // incident i e}, f z.val :=
      (incidentEquiv i).symm.sum_comp (fun z => f z.val)
    _ = _ := by
      apply Fintype.sum_of_injective
        (fun z : {e : Edge r // incident i e} => z.val) Subtype.val_injective
        (fun z => f z.val) (fun e => if incident i e then f e else 0)
      · intro e he
        have hi : ¬incident i e := by
          intro hi
          exact he ⟨⟨e, hi⟩, rfl⟩
        simp [hi]
      · intro z
        simp [z.property]

theorem neighbor_sum {r : ℕ} (i : Fin r) (f : Edge r → ℝ) :
    (∑ j : Fin r, if h : i = j then 0 else f (edge i j h)) =
      ∑ e : Edge r, if incident i e then f e else 0 := by
  classical
  rw [← incident_sum]
  symm
  apply Fintype.sum_of_injective
    (fun j : {j : Fin r // j ≠ i} => j.val) Subtype.val_injective
    (fun j => f (edge i j.val j.property.symm))
    (fun j => if h : i = j then 0 else f (edge i j h))
  · intro j hj
    have hji : j = i := by
      by_contra hji
      exact hj ⟨⟨j, hji⟩, rfl⟩
    simp [hji]
  · intro j
    simp [j.property.symm]

theorem K_row {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ) (i : Fin r) :
    UniformSchmidtDefectMoment.rowSum (K t b) i =
      (∑ e, topWeight i e * t e) + (∑ p, bottomWeight i p * b p) := by
  classical
  have hp (j : Fin r) : K t b i j =
      (if i = j then 2 * b (.inl i) else 0) +
      (if h : i = j then 0 else b (.inr (edge i j h)) - t (edge i j h)) := by
    by_cases h : i = j <;> simp [K, h]
  have hrow : UniformSchmidtDefectMoment.rowSum (K t b) i =
      2 * b (.inl i) +
        ∑ e : Edge r, if incident i e then b (.inr e) - t e else 0 := by
    unfold UniformSchmidtDefectMoment.rowSum
    simp_rw [hp]
    rw [sum_add_distrib, Fintype.sum_ite_eq i (fun _ => 2 * b (.inl i))]
    rw [neighbor_sum i (fun e => b (.inr e) - t e)]
  have hs : (∑ e : Edge r, if incident i e then b (.inr e) - t e else 0) =
      (∑ e, topWeight i e * t e) +
        (∑ e, (if incident i e then (1 : ℝ) else 0) * b (.inr e)) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro e _
    by_cases hi : incident i e <;> simp [topWeight, hi] <;> ring
  rw [hrow, hs]
  simp only [Fintype.sum_sum_type, bottomWeight]
  have hd : (∑ j : Fin r, (if i = j then (2 : ℝ) else 0) * b (.inl j)) =
      2 * b (.inl i) := by simp
  rw [hd]
  ring

theorem top_column_sum {r : ℕ} (e : Edge r) :
    (∑ i : Fin r, topWeight i e) = -2 := by
  classical
  have hp (i : Fin r) : topWeight i e =
      -(if i = e.val.1 then (1 : ℝ) else 0) -
        (if i = e.val.2 then (1 : ℝ) else 0) := by
    have hne := ne_of_lt e.property
    by_cases ha : i = e.val.1 <;> by_cases hb : i = e.val.2 <;>
      simp_all [topWeight, incident]
  simp_rw [hp]
  norm_num

theorem bottom_column_sum {r : ℕ} (p : BottomSlot r) :
    (∑ i : Fin r, bottomWeight i p) = 2 := by
  classical
  rcases p with j | e
  · simp [bottomWeight]
  · have hp (i : Fin r) : bottomWeight i (.inr e) = -topWeight i e := by
      by_cases hi : incident i e <;> simp [bottomWeight, topWeight, hi]
    simp_rw [hp]
    rw [sum_neg_distrib, top_column_sum]
    norm_num

theorem K_charge {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ) :
    UniformSchmidtDefectMoment.uniformCharge (K t b) =
      2 * ((∑ p, b p) - ∑ e, t e) := by
  classical
  unfold UniformSchmidtDefectMoment.uniformCharge
  simp_rw [K_row]
  rw [sum_add_distrib]
  rw [sum_comm (f := fun i e => topWeight i e * t e)]
  rw [sum_comm (f := fun i p => bottomWeight i p * b p)]
  simp_rw [← sum_mul, top_column_sum, bottom_column_sum]
  rw [← mul_sum, ← mul_sum]
  ring

theorem K_trace {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ) :
    (K t b).trace = 2 * ∑ i, b (.inl i) := by
  simp [Matrix.trace, Matrix.diag_apply, K, mul_sum]

/-- Scalar cancellations after the ACTUAL graph counts above; no division by s. -/
theorem incidence_factors {r : ℕ} (hr : 3 ≤ r) :
    let a : ℝ := Fintype.card (Edge r)
    let b : ℝ := Fintype.card (BottomSlot r)
    (a * ((r : ℝ) - 1) - (-((r : ℝ) - 1))^2) / (a * (a - 1)) =
        2 * ((r : ℝ) - 1) / ((r : ℝ) * ((r : ℝ) + 1)) ∧
    (b * ((r : ℝ) + 3) - ((r : ℝ) + 1)^2) / (b * (b - 1)) =
        2 / (r : ℝ) := by
  dsimp only
  rw [edge_card_real, bottom_card_real]
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (r : ℝ) ≠ 0 := by linarith
  have hr1 : (r : ℝ) + 1 ≠ 0 := by linarith
  have ha0 : (r : ℝ) * ((r : ℝ) - 1) / 2 ≠ 0 := by nlinarith
  have ha1 : (r : ℝ) * ((r : ℝ) - 1) / 2 - 1 ≠ 0 := by nlinarith
  have hb0 : (r : ℝ) * ((r : ℝ) + 1) / 2 ≠ 0 := by nlinarith
  have hb1 : (r : ℝ) * ((r : ℝ) + 1) / 2 - 1 ≠ 0 := by nlinarith
  constructor
  · apply (div_eq_div_iff (mul_ne_zero ha0 ha1) (mul_ne_zero hr0 hr1)).2
    ring
  · apply (div_eq_div_iff (mul_ne_zero hb0 hb1) hr0).2
    ring

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtIncidence
