/- GID: D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseLDUI
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricExtensions/BoseLDUI
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact normalized Dicke and LDUI coordinates, including the off-diagonal half. -/

import D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseRootTranspose
import D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseCoherentSymbol

/-! These are the actual normalized Dicke vectors in the existing tensor
model. Coordinates agree with Gulati--Nechita--Park, Section 2.4.
The application note is by Haobo Ma, then Wenlin Zhang. -/

open scoped BigOperators ComplexOrder
open Matrix
open D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseRootTranspose
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl
open D5.S3.Quantum.Entanglement.OccupancyWordSectors

namespace D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseLDUI

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- The actual LDUI Dicke operator with diagonal weight P_ii and
off-diagonal normalized-Dicke weight 2 P_ij. -/
def ldui (P : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  dickeOperator (fun i j => if i = j then P i i else 2 * P i j)

open private dicke_pair_supported from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

private lemma ldui_bose (P : Matrix (Fin n) (Fin n) ℝ) :
    pairSymmetricProjector * ldui P * pairSymmetricProjector = ldui P :=
  dicke_pair_supported _

private lemma dickeVector_zero_of_indices (i j a b : Fin n) (hij : i ≤ j)
    (h : i ≠ min a b ∨ j ≠ max a b) : dickeVector i j (a,b) = 0 := by
  have h₁ : (a,b) ≠ (i,j) := by
    rintro ⟨⟩
    simp [min_eq_left hij,max_eq_right hij] at h
  have h₂ : (a,b) ≠ (j,i) := by
    rintro ⟨⟩
    simp [min_eq_right hij,max_eq_left hij] at h
  by_cases he : i = j
  · subst j
    simp [dickeVector,h₁]
  · simp [dickeVector,he,h₁,h₂]

private lemma dickeOperator_entry_reduction (Y : Fin n → Fin n → ℝ)
    (a b c d : Fin n) :
    dickeOperator Y (a,b) (c,d) =
      (Y (min a b) (max a b) : ℂ) *
        (dickeVector (min a b) (max a b) (a,b) *
          star (dickeVector (min a b) (max a b) (c,d))) := by
  simp only [dickeOperator,Matrix.sum_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,
    Pi.star_apply,smul_eq_mul]
  rw [Finset.sum_eq_single (min a b)]
  · rw [Finset.sum_eq_single (max a b)]
    · simp [min_le_max,Matrix.vecMulVec_apply,Pi.star_apply]
    · intro j hj hje
      by_cases hij : min a b ≤ j
      · simp [hij,Matrix.vecMulVec_apply,Pi.star_apply,
          dickeVector_zero_of_indices _ _ a b hij (Or.inr hje)]
      · simp [hij]
    · simp
  · intro i hi hie
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hij : i ≤ j
    · simp [hij,Matrix.vecMulVec_apply,Pi.star_apply,
        dickeVector_zero_of_indices _ _ a b hij (Or.inl hie)]
    · simp [hij]
  · simp

private lemma ldui_entry (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.IsSymm)
    (a b c d : Fin n) :
    ldui P (a,b) (c,d) =
      if (c = a ∧ d = b) ∨ (c = b ∧ d = a) then (P a b : ℂ) else 0 := by
  have hs : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [← _root_.mul_inv_rev]
    congr 1
    norm_cast
    exact Real.mul_self_sqrt (by norm_num)
  have hs' : ((Real.sqrt 2 : ℂ)⁻¹)^2 = (2 : ℂ)⁻¹ := by
    simpa only [pow_two] using hs
  rw [ldui,dickeOperator_entry_reduction]
  by_cases hab : a ≤ b
  · simp only [min_eq_left hab,max_eq_right hab]
    by_cases he : a = b
    · subst b
      simp [dickeVector,Prod.mk.injEq,and_comm]
    · simp only [he,if_false,dickeVector,Complex.star_def,map_mul,Complex.conj_ofReal,
        map_add,apply_ite,map_one,map_zero,Prod.mk.injEq]
      by_cases h₁ : c = a ∧ d = b <;> by_cases h₂ : c = b ∧ d = a <;>
        simp [h₁,h₂,he,Ne.symm he,apply_ite] <;> ring_nf <;> simp [hs']
  · have hba : b ≤ a := le_of_not_ge hab
    have he : b ≠ a := by intro h; subst a; exact hab le_rfl
    simp only [min_eq_right hba,max_eq_left hba,he,if_false,dickeVector,
      Complex.star_def,map_mul,Complex.conj_ofReal,map_add,apply_ite,map_one,map_zero,
      Prod.mk.injEq,hP.apply a b]
    by_cases h₁ : c = a ∧ d = b <;> by_cases h₂ : c = b ∧ d = a <;>
      simp [h₁,h₂,he,Ne.symm he,apply_ite] <;> ring_nf <;> simp [hs']

private lemma ldui_hermitian (P : Matrix (Fin n) (Fin n) ℝ) :
    (ldui P).IsHermitian := by
  unfold ldui dickeOperator
  change (∑ i, ∑ j, _)ᴴ = _
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs
  · exact ((Matrix.posSemidef_vecMulVec_self_star _).1.smul (by
      simp only [isSelfAdjoint_iff,Complex.star_def,Complex.conj_ofReal])).eq
  · exact Matrix.isHermitian_zero.eq

private def pairAction (u : Fin n → ℂ)
    (A : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :=
  diagonal (fun v : Fin n × Fin n => u v.1 * u v.2) * A *
    (diagonal (fun v : Fin n × Fin n => u v.1 * u v.2))ᴴ

private def pairTwirl (A : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :=
  (Fintype.card (Fin n → ZMod 3) : ℝ)⁻¹ •
    ∑ t : Fin n → ZMod 3, pairAction (occupationPhase (r := 2) t) A

private lemma pair_occupation (a b : Fin n) :
    occupation ![a,b] = ([a,b] : List (Fin n)) := by
  simp [occupation,List.ofFn_succ]

private lemma pair_occupation_eq (a b c d : Fin n) :
    occupation ![a,b] = occupation ![c,d] ↔
      (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  rw [pair_occupation,pair_occupation,Multiset.coe_eq_coe,List.pair_perm]
  simp only [List.cons.injEq,and_true]

private lemma pairTwirl_apply
    (A : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (a b c d : Fin n) :
    pairTwirl A (a,b) (c,d) =
      if (c = a ∧ d = b) ∨ (c = b ∧ d = a) then A (a,b) (c,d) else 0 := by
  have hor := occupation_character_orthogonality ![a,b] ![c,d]
  have hor' : (∑ t : Fin n → ZMod 3,
      (occupationPhase t a * occupationPhase t b) *
        star (occupationPhase t c * occupationPhase t d)) =
      if (c = a ∧ d = b) ∨ (c = b ∧ d = a) then
        (Fintype.card (Fin n → ZMod 3) : ℂ) else 0 := by
    simpa [tensorPhase,Fin.prod_univ_two,pair_occupation_eq] using hor
  simp only [pairTwirl,pairAction,Matrix.smul_apply,Matrix.sum_apply,
    Matrix.diagonal_conjTranspose,Matrix.diagonal_mul,Matrix.mul_diagonal,Pi.star_apply]
  have he : (∑ t : Fin n → ZMod 3,
      (occupationPhase t a * occupationPhase t b) * A (a,b) (c,d) *
        star (occupationPhase t c * occupationPhase t d)) =
      (∑ t : Fin n → ZMod 3,
        (occupationPhase t a * occupationPhase t b) *
          star (occupationPhase t c * occupationPhase t d)) * A (a,b) (c,d) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [he,hor']
  split_ifs
  · change (((Fintype.card (Fin n → ZMod 3) : ℝ)⁻¹ : ℝ) : ℂ) *
      ((Fintype.card (Fin n → ZMod 3) : ℂ) * A (a,b) (c,d)) = _
    rw [Complex.ofReal_inv,Complex.ofReal_natCast,← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),one_mul]
  · simp only [zero_mul,smul_zero]

private lemma pairTwirl_hermitian
    (A : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hA : A.IsHermitian) :
    (pairTwirl A).IsHermitian := by
  apply Matrix.IsHermitian.smul ?_ (IsSelfAdjoint.all _)
  change (∑ t, pairAction (occupationPhase (r := 2) t) A)ᴴ = _
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact (Matrix.isHermitian_mul_mul_conjTranspose _ hA).eq

private lemma trace_pairAction
    (u : Fin n → ℂ) (A B : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    (pairAction u A * B).trace = (A * pairAction (star u) B).trace := by
  unfold pairAction
  have hd : diagonal (fun v : Fin n × Fin n => star u v.1 * star u v.2) =
      (diagonal (fun v : Fin n × Fin n => u v.1 * u v.2))ᴴ := by
    rw [diagonal_conjTranspose]
    congr 1
    funext v
    simp only [Pi.star_apply,star_mul]
    exact mul_comm _ _
  rw [hd,conjTranspose_conjTranspose]
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_comm (diagonal (fun v : Fin n × Fin n => u v.1 * u v.2))
      (A * (diagonal (fun v : Fin n × Fin n => u v.1 * u v.2))ᴴ * B)

private lemma ldui_row_sum (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.IsSymm)
    (a b : Fin n) (f : Fin n × Fin n → ℂ) :
    (∑ w, ldui P (a,b) w * f w) =
      if a = b then (P a a : ℂ) * f (a,a)
      else (P a b : ℂ) * (f (a,b) + f (b,a)) := by
  by_cases hab : a = b
  · subst b
    rw [Finset.sum_eq_single (a,a)]
    · simp [ldui_entry,hP]
    · rintro ⟨c,d⟩ hw hne
      have hcd : ¬ (c = a ∧ d = a) := fun h => hne (Prod.ext h.1 h.2)
      simp [ldui_entry,hP,hcd]
    · simp
  · have hne : (a,b) ≠ (b,a) := by
      intro h
      exact hab (congrArg Prod.fst h)
    rw [Finset.sum_eq_add_of_mem (a,b) (b,a) (Finset.mem_univ _) (Finset.mem_univ _) hne]
    · simp [ldui_entry,hP,hab]
      ring
    · rintro ⟨c,d⟩ hw ⟨h₁,h₂⟩
      have hc₁ : ¬ (c = a ∧ d = b) := fun h => h₁ (Prod.ext h.1 h.2)
      have hc₂ : ¬ (c = b ∧ d = a) := fun h => h₂ (Prod.ext h.1 h.2)
      simp [ldui_entry,hP,hc₁,hc₂]

private lemma pairTwirl_reconstruction
    (A : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hA : A.IsHermitian)
    (hs : ∀ v w, A v.swap w = A v w) :
    ∃ R : Matrix (Fin n) (Fin n) ℝ, R.IsSymm ∧ pairTwirl A = ldui R := by
  have hc (v w : Fin n × Fin n) : A v w.swap = A v w := by
    calc
      A v w.swap = star (A w.swap v) := (hA.apply _ _).symm
      _ = star (A w v) := congrArg star (hs w v)
      _ = A v w := hA.apply _ _
  let R : Matrix (Fin n) (Fin n) ℝ := fun i j => (A (i,j) (i,j)).re
  have hR : R.IsSymm := by
    ext i j
    change (A (j,i) (j,i)).re = (A (i,j) (i,j)).re
    rw [← hc (j,i) (j,i)]
    exact congrArg Complex.re (hs (i,j) (i,j))
  refine ⟨R,hR,?_⟩
  ext ⟨a,b⟩ ⟨c,d⟩
  rw [pairTwirl_apply,ldui_entry R hR]
  split_ifs with h
  · have he : A (a,b) (c,d) = A (a,b) (a,b) := by
      rcases h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · simp only [h₁,h₂]
      · simpa only [h₁,h₂,Prod.swap_prod_mk] using hc (a,b) (a,b)
    rw [he]
    exact ((RCLike.conj_eq_iff_re (K := ℂ)).mp (hA.apply (a,b) (a,b))).symm
  · rfl

private def dualCoordinates (R : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => if i = j then R i i else 2 * R i j

private lemma dualCoordinates_symm (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm) :
    (dualCoordinates R).IsSymm := by
  ext i j
  by_cases h : i = j
  · subst j; rfl
  · simp [dualCoordinates,h,Ne.symm h,hR.apply i j]

private lemma ldui_trace_pairing (P R : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.IsSymm) (hR : R.IsSymm) :
    (ldui P * ldui R).trace = ((∑ i, ∑ j, P i j * dualCoordinates R i j : ℝ) : ℂ) := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Fintype.sum_prod_type,
    Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hh := ldui_row_sum P hP i j (fun w => ldui R w (i,j))
  rw [Fintype.sum_prod_type] at hh
  rw [hh]
  by_cases hij : i = j
  · subst j
    simp [ldui_entry,hR,dualCoordinates]
  · simp [hij,ldui_entry,hR,dualCoordinates,hR.apply i j]
    ring_nf
    simp

private lemma ldui_coherent (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm)
    (z : Fin n → ℂ) :
    star (fun v : Fin n × Fin n => z v.1 * z v.2) ⬝ᵥ
      (ldui R *ᵥ (fun v => z v.1 * z v.2)) =
        ∑ i, ∑ j, (dualCoordinates R i j : ℂ) *
          (star (z i) * z i) * (star (z j) * z j) := by
  simp only [dotProduct,Matrix.mulVec,Pi.star_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [ldui_row_sum R hR]
  by_cases hij : i = j
  · subst j
    simp [dualCoordinates,star_mul]
    ring
  · simp [hij,dualCoordinates,star_mul]
    ring


end
end D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseLDUI
