/- GID: D5/S3/Combinatorics/Graph/MixedAdjacency
   generality: G
   mirror-B: none(waiver:covered-by-mixed-power-graft-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The largest real eigenvalue of the mixed degree–adjacency matrix. -/

import OmegaBuild.Commands
import D5.S3.LinearAlgebra.Matrix.RealRayleigh
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-! Omega original. The largest real eigenvalue of the mixed degree–adjacency matrix. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix Finset SimpleGraph OmegaMath.RealRayleigh

noncomputable section

namespace OmegaMath.MixedAdjacency

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

local instance graphDecidable' {U : Type*} (G : SimpleGraph U) : DecidableRel G.Adj :=
  Classical.decRel _

def mixedMatrix (G : SimpleGraph V) (α : ℝ) : Matrix V V ℝ :=
  α • G.degMatrix ℝ + (1 - α) • G.adjMatrix ℝ

def mixedTop (G : SimpleGraph V) (α : ℝ) : ℝ :=
  topEigenvalue (mixedMatrix G α)

theorem mixedMatrix_hermitian (G : SimpleGraph V) (α : ℝ) :
    (mixedMatrix G α).IsHermitian := by
  exact (G.isHermitian_degMatrix ℝ).smul (by simp [IsSelfAdjoint] : IsSelfAdjoint α) |>.add
    ((G.isHermitian_adjMatrix ℝ).smul (by simp [IsSelfAdjoint] : IsSelfAdjoint (1 - α)))

theorem mixedMatrix_apply (G : SimpleGraph V) (α : ℝ) (i j : V) :
    mixedMatrix G α i j =
      if i = j then α * (G.degree i : ℝ) else if G.Adj i j then 1 - α else 0 := by
  by_cases h : i = j
  · subst j
    simp [mixedMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply]
  · simp [mixedMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply, h]

private theorem mixedMatrix_nonneg (G : SimpleGraph V) {α : ℝ}
    (hα : 0 ≤ α) (hα' : α ≤ 1) (i j : V) :
    0 ≤ mixedMatrix G α i j := by
  rw [mixedMatrix_apply]
  split
  · positivity
  · split
    · linarith
    · rfl

private theorem mixedMatrix_adj (G : SimpleGraph V) (α : ℝ) {i j : V} (h : G.Adj i j) :
    mixedMatrix G α i j = 1 - α := by
  simp [mixedMatrix_apply, h.ne, h]

theorem mixedTop_isGreatest [Nonempty V] (G : SimpleGraph V) (α : ℝ) :
    IsGreatest (spectrum ℝ (mixedMatrix G α)) (mixedTop G α) :=
  top_isGreatest _ (mixedMatrix_hermitian G α)

theorem mixed_nonnegative_maximizer [Nonempty V] (G : SimpleGraph V) {α : ℝ}
    (hα : 0 ≤ α) (hα' : α ≤ 1) :
    ∃ x : V → ℝ, UnitVector x ∧ energy (mixedMatrix G α) x = mixedTop G α ∧
      mixedMatrix G α *ᵥ x = mixedTop G α • x ∧ ∀ i, 0 ≤ x i :=
  nonnegative_maximizer _ (mixedMatrix_hermitian G α) (mixedMatrix_nonneg G hα hα')

theorem mixed_positive_maximizer [Nonempty V] (G : SimpleGraph V)
    (hc : G.Connected) {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1) :
    ∃ x : V → ℝ, UnitVector x ∧ energy (mixedMatrix G α) x = mixedTop G α ∧
      mixedMatrix G α *ᵥ x = mixedTop G α • x ∧ ∀ i, 0 < x i := by
  obtain ⟨x, hx, he, hev, hnn⟩ := mixed_nonnegative_maximizer G hα hα'.le
  refine ⟨x, hx, he, hev, ?_⟩
  have hprop (i j : V) (hij : G.Adj i j) (hi : x i = 0) : x j = 0 := by
    have hz : ∑ l, mixedMatrix G α i l * x l = 0 := by
      have hrow := congrFun hev i
      simpa [Matrix.mulVec, dotProduct, hi] using hrow
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun l _ => mul_nonneg (mixedMatrix_nonneg G hα hα'.le i l) (hnn l))).mp hz j (mem_univ j)
    rw [mixedMatrix_adj G α hij] at hterm
    exact (mul_eq_zero.mp hterm).resolve_left (by linarith)
  have hwalk {u v : V} (p : G.Walk u v) : x u = 0 → x v = 0 := by
    induction p with
    | nil => exact id
    | cons hadj p ih => exact fun hz => ih (hprop _ _ hadj hz)
  intro i
  by_contra! hn
  have hi : x i = 0 := le_antisymm hn (hnn i)
  have hall (j : V) : x j = 0 := by
    obtain ⟨p⟩ := hc.preconnected i j
    exact hwalk p hi
  simp [UnitVector, hall] at hx

private theorem mixedMatrix_mono {G H : SimpleGraph V} (hle : G ≤ H) {α : ℝ}
    (hα : 0 ≤ α) (hα' : α ≤ 1) (i j : V) :
    mixedMatrix G α i j ≤ mixedMatrix H α i j := by
  rw [mixedMatrix_apply, mixedMatrix_apply]
  by_cases hij : i = j
  · simp only [hij, ite_true]
    apply mul_le_mul_of_nonneg_left _ hα
    exact_mod_cast G.degree_le_of_le (v := i) hle
  · simp only [hij, ite_false]
    by_cases hg : G.Adj i j
    · simp [hg, hle hg]
    · simp only [hg, ite_false]
      split <;> linarith

theorem mixedTop_mono [Nonempty V] {G H : SimpleGraph V} (hle : G ≤ H)
    {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 1) :
    mixedTop G α ≤ mixedTop H α := by
  obtain ⟨x, hx, he, _, hnn⟩ := mixed_nonnegative_maximizer G hα hα'
  rw [← he]
  apply le_trans _ (energy_le_top (mixedMatrix H α) hx)
  rw [energy_expand, energy_expand]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (mixedMatrix_mono hle hα hα' i j) (mul_nonneg (hnn i) (hnn j))

theorem mixedTop_strict [Nonempty V] {G H : SimpleGraph V} (hlt : G < H)
    (hc : G.Connected) {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1) :
    mixedTop G α < mixedTop H α := by
  obtain ⟨x, hx, he, _, hp⟩ := mixed_positive_maximizer G hc hα hα'
  have hnot : ¬ H ≤ G := not_le_of_gt hlt
  simp only [SimpleGraph.le_iff_adj, not_forall] at hnot
  obtain ⟨u, v, huv, hnuv⟩ := hnot
  have hentry : mixedMatrix G α u v < mixedMatrix H α u v := by
    rw [mixedMatrix_adj H α huv, mixedMatrix_apply]
    simp [huv.ne, hnuv]
    linarith
  have hle (i j : V) : mixedMatrix G α i j * (x i * x j) ≤
      mixedMatrix H α i j * (x i * x j) :=
    mul_le_mul_of_nonneg_right (mixedMatrix_mono hlt.le hα hα'.le i j)
      (mul_nonneg (hp i).le (hp j).le)
  rw [← he]
  apply lt_of_lt_of_le _ (energy_le_top (mixedMatrix H α) hx)
  rw [energy_expand, energy_expand]
  apply Finset.sum_lt_sum (fun i _ => Finset.sum_le_sum (fun j _ => hle i j))
  refine ⟨u, mem_univ _, ?_⟩
  apply Finset.sum_lt_sum (fun j _ => hle u j)
  exact ⟨v, mem_univ _, mul_lt_mul_of_pos_right hentry (mul_pos (hp u) (hp v))⟩

private theorem mixedMatrix_symm (G : SimpleGraph V) (α : ℝ) :
    (mixedMatrix G α).IsSymm := by
  exact (G.isSymm_degMatrix ℝ).smul α |>.add ((G.isSymm_adjMatrix (α := ℝ)).smul (1 - α))

private theorem mixedMatrix_const_one (G : SimpleGraph V) (α : ℝ) (i : V) :
    (mixedMatrix G α *ᵥ (fun _ => 1)) i = (G.degree i : ℝ) := by
  rw [mixedMatrix, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
  change α * (G.degMatrix ℝ *ᵥ (fun _ => 1)) i +
    (1 - α) * (G.adjMatrix ℝ *ᵥ (Function.const _ 1)) i = _
  rw [G.degMatrix_mulVec_apply, SimpleGraph.adjMatrix_mulVec_const_apply]
  ring

private theorem mixedTop_regular [Nonempty V] (G : SimpleGraph V) (hc : G.Connected)
    (d : ℕ) (hd : ∀ i, G.degree i = d)
    {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1) :
    mixedTop G α = (d : ℝ) := by
  obtain ⟨x, _, _, hev, hp⟩ := mixed_positive_maximizer G hc hα hα'
  let A := mixedMatrix G α
  let one : V → ℝ := fun _ => 1
  have hrow : A *ᵥ one = fun _ => (d : ℝ) := by
    ext i
    exact (mixedMatrix_const_one G α i).trans (by rw [hd])
  have hsym : Aᵀ = A := mixedMatrix_symm G α
  have hdot : one ⬝ᵥ (A *ᵥ x) = (A *ᵥ one) ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym]
  change one ⬝ᵥ (mixedMatrix G α *ᵥ x) = (A *ᵥ one) ⬝ᵥ x at hdot
  rw [hev, hrow] at hdot
  have hsum : 0 < ∑ i, x i := Finset.sum_pos (fun i _ => hp i) univ_nonempty
  simp only [dotProduct, one, Pi.smul_apply, smul_eq_mul, one_mul, ← Finset.mul_sum] at hdot
  exact (mul_left_inj' hsum.ne').mp hdot

private theorem mixedTop_complete [Nonempty V] {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1) :
    mixedTop (⊤ : SimpleGraph V) α = (Fintype.card V : ℝ) - 1 := by
  refine (mixedTop_regular (⊤ : SimpleGraph V) SimpleGraph.connected_top
    (Fintype.card V - 1) ?_ hα hα').trans ?_
  · intro i
    convert SimpleGraph.complete_graph_degree i using 2
  · simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℝ) (show 1 ≤ Fintype.card V from Fintype.card_pos))

theorem mixedTop_le_complete [Nonempty V] (G : SimpleGraph V)
    {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1) :
    mixedTop G α ≤ (Fintype.card V : ℝ) - 1 :=
  (mixedTop_mono le_top hα hα'.le).trans_eq (mixedTop_complete hα hα')

theorem mixedTop_eq_complete_iff [Nonempty V] (G : SimpleGraph V) (hc : G.Connected)
    {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1) :
    mixedTop G α = (Fintype.card V : ℝ) - 1 ↔ G = ⊤ := by
  rw [← mixedTop_complete (V := V) hα hα']
  constructor
  · intro he
    by_contra! hn
    have hlt : G < ⊤ := lt_of_le_of_ne le_top hn
    exact (mixedTop_strict hlt hc hα hα').ne he
  · rintro rfl
    rfl

private theorem mixedMatrix_iso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (α : ℝ) (i j : V) :
    mixedMatrix G α i j = mixedMatrix H α (e i) (e j) := by
  rw [mixedMatrix_apply, mixedMatrix_apply, e.degree_eq i]
  simp [e.injective.eq_iff, e.map_adj_iff]

private theorem mixedTop_le_of_iso [Nonempty V] [Nonempty W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) (α : ℝ) :
    mixedTop G α ≤ mixedTop H α := by
  obtain ⟨x, hx, he, _⟩ := top_attained (mixedMatrix G α)
  let y : W → ℝ := fun i => x (f.symm i)
  have hxy (i : V) : y (f i) = x i := by simp [y]
  have hy : UnitVector y := by
    rw [UnitVector, ← f.toEquiv.sum_comp (fun i => y i ^ 2)]
    change ∑ i, y (f i) ^ 2 = 1
    simpa only [hxy] using (show ∑ i, x i ^ 2 = 1 from hx)
  have henergy : energy (mixedMatrix G α) x = energy (mixedMatrix H α) y := by
    rw [energy_expand, energy_expand, ← f.toEquiv.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    rw [← f.toEquiv.sum_comp]
    apply Finset.sum_congr rfl
    intro j _
    change mixedMatrix G α i j * (x i * x j) =
      mixedMatrix H α (f i) (f j) * (y (f i) * y (f j))
    rw [hxy, hxy, mixedMatrix_iso f]
  calc
    mixedTop G α = energy (mixedMatrix G α) x := he.symm
    _ = energy (mixedMatrix H α) y := henergy
    _ ≤ mixedTop H α := energy_le_top _ hy

theorem mixedTop_iso [Nonempty V] [Nonempty W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (α : ℝ) :
    mixedTop G α = mixedTop H α :=
  le_antisymm (mixedTop_le_of_iso e α) (mixedTop_le_of_iso e.symm α)

end OmegaMath.MixedAdjacency
