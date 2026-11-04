/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelComplementaryMinor
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelComplementaryMinor
   mirror-E: none(waiver:shifted-hankel-complementary-boundary)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Fin]
   utility: none
   digest: Exact ordered complementary indices and signs reduce shifted Hankel minors to boundary determinants. -/

import D5.S3.Arith.AbsoluteValues.Heights.Duality
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelBoundaryPolynomials
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelDefs
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

/-! Ordered complementary minors at a supported Hankel boundary. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelComplementaryMinor

open Finset
open scoped Matrix

/-- Put the shifted target columns first, followed by their two ordered boundary pieces. -/
def columnPerm (a j u : ℕ) : Equiv.Perm (Fin (j + (a + u))) where
  toFun i := ⟨if i.val < j then a + i.val else if i.val < j + a then i.val - j else i.val,
    by split_ifs <;> omega⟩
  invFun i := ⟨if i.val < a then j + i.val else if i.val < a + j then i.val - a else i.val,
    by split_ifs <;> omega⟩
  left_inv i := by apply Fin.ext; dsimp; split_ifs <;> omega
  right_inv i := by apply Fin.ext; dsimp; split_ifs <;> omega

/-- The increasing complement of the shifted target interval. -/
def boundaryIndex (a j u : ℕ) (i : Fin (a + u)) : Fin (j + (a + u)) :=
  ⟨if i.val < a then i.val else j + i.val, by split_ifs <;> omega⟩

private theorem column_sign (a j u : ℕ) :
    (columnPerm a j u).sign = (-1 : ℤˣ) ^ (a * j) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  have inner (i : Fin (j + (a + u))) :
      (∏ k ∈ Ioi i, if columnPerm a j u i < columnPerm a j u k then (1 : ℤˣ) else -1) =
        if i.val < j then (-1 : ℤˣ) ^ a else 1 := by
    rw [show Ioi i = univ.filter (fun k => i < k) by ext k; simp]
    rw [prod_filter]
    have term (k : Fin (j + (a + u))) :
        (if i < k then (if columnPerm a j u i < columnPerm a j u k then (1 : ℤˣ) else -1) else 1) =
          if i.val < j ∧ j ≤ k.val ∧ k.val < j + a then -1 else 1 := by
      simp only [Fin.lt_def, columnPerm, Equiv.coe_fn_mk, Fin.val_mk]
      split_ifs <;> first | rfl | omega
    simp_rw [term]
    rw [Fin.prod_univ_add]
    have first : (∏ k : Fin j,
        if i.val < j ∧ j ≤ (Fin.castAdd (a + u) k).val ∧
          (Fin.castAdd (a + u) k).val < j + a then (-1 : ℤˣ) else 1) = 1 := by
      apply prod_eq_one; intro k _; simp
    rw [first, one_mul, Fin.prod_univ_add]
    by_cases hi : i.val < j
    · simp [hi, Fin.val_natAdd, Fin.val_castAdd, show ∀ k : Fin a, j + k.val < j + a by intro k; omega,
        show ∀ k : Fin u, ¬ j + (a + k.val) < j + a by intro k; omega]
    · simp [hi]
  simp_rw [inner]
  rw [Fin.prod_univ_add]
  simp [Fin.val_castAdd, Fin.val_natAdd, show ∀ i : Fin j, i.val < j from fun i => i.isLt,
    show ∀ i : Fin (a + u), ¬ j + i.val < j by intro i; omega, ← pow_mul, Nat.mul_comm]

private theorem boundary_mono (a j u : ℕ) : StrictMono (boundaryIndex a j u) := by
  intro i k hik
  simp only [Fin.lt_def, boundaryIndex, Fin.val_mk] at *
  split_ifs <;> omega

/-- Ordered interval-minor reduction. The inverse rows are the two boundary pieces;
the inverse columns are the final a+u columns. No selected-minor unit is assumed. -/
private theorem shifted_minor (a j u : ℕ)
    (H : Matrix (Fin (j + (a + u))) (Fin (j + (a + u))) ℤ)
    (hH : IsUnit H.det) :
    (Matrix.of fun i k : Fin j => H ⟨i.val, by omega⟩ ⟨a + k.val, by omega⟩).det =
      (-1 : ℤ) ^ (a * j) * H.det *
        (Matrix.of fun i k : Fin (a + u) =>
          H⁻¹ (boundaryIndex a j u i) ⟨j + k.val, by omega⟩).det := by
  classical
  let e : Fin j ⊕ Fin (a + u) ≃ Fin (j + (a + u)) := finSumFinEquiv
  let s : Finset (Fin (j + (a + u))) := univ.image
    (fun i : Fin j => (⟨a + i.val, by omega⟩ : Fin (j + (a + u))))
  have inj : Function.Injective (fun i : Fin j =>
      (⟨a + i.val, by omega⟩ : Fin (j + (a + u)))) := by
    intro i k h; apply Fin.ext; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
  have hs : s.card = j := by dsimp [s]; rw [card_image_of_injective _ inj, card_univ, Fintype.card_fin]
  have hsc : sᶜ.card = a + u := by rw [card_compl, hs, Fintype.card_fin]; omega
  have selected (i : Fin j) : s.orderEmbOfFin hs i = ⟨a + i.val, by omega⟩ := by
    apply congrFun (orderEmbOfFin_unique hs (fun i => mem_image.mpr ⟨i, mem_univ _, rfl⟩) ?_).symm i
    intro i k h; simpa only [Fin.lt_def, Fin.val_mk, Nat.add_lt_add_iff_left] using h
  have complement (i : Fin (a + u)) : sᶜ.orderEmbOfFin hsc i = boundaryIndex a j u i := by
    apply congrFun (orderEmbOfFin_unique hsc ?_ (boundary_mono a j u)).symm i
    intro i
    rw [mem_compl]; change ¬ _ ∈ univ.image _; rw [mem_image]
    rintro ⟨k, _, hk⟩
    have hh := congrArg Fin.val hk
    dsimp [boundaryIndex] at hh
    split_ifs at hh <;> omega
  let C := H.submatrix e id
  let D := H⁻¹.transpose.submatrix e id
  have dual : C * D.transpose = 1 := by
    dsimp [C, D]
    rw [Matrix.transpose_submatrix, Matrix.transpose_transpose]
    calc
      _ = (H * H⁻¹).submatrix e e := by
        simpa only [Equiv.coe_refl] using
          (Matrix.submatrix_mul_equiv H H⁻¹ e (Equiv.refl _) e)
      _ = 1 := by rw [Matrix.mul_nonsing_inv H hH, Matrix.submatrix_one_equiv]
  have jacobi := Matrix.det_submatrix_inl_eq_mul C D dual hs hsc
  have enum : Matrix.enumEquiv hs hsc = e.trans (columnPerm a j u) := by
    ext i
    rcases i with i | i
    · simp [Matrix.enumEquiv, e, selected, columnPerm]
    · simp [Matrix.enumEquiv, e, complement, columnPerm, boundaryIndex]
  have factor : (C.submatrix id (Matrix.enumEquiv hs hsc)).det =
      (-1 : ℤ) ^ (a * j) * H.det := by
    rw [enum]
    have eqm : C.submatrix id (e.trans (columnPerm a j u)) =
        (H.submatrix id (columnPerm a j u)).submatrix e e := by rfl
    rw [eqm, Matrix.det_submatrix_equiv_self, Matrix.det_permute', column_sign]
    simp
  rw [factor] at jacobi
  have left : ((C.submatrix Sum.inl id).submatrix id (s.orderEmbOfFin hs)) =
      Matrix.of (fun i k : Fin j => H ⟨i.val, by omega⟩ ⟨a + k.val, by omega⟩) := by
    ext i k; simpa [C, e, selected] using (show H (Fin.castAdd (a + u) i) ⟨a + k.val, by omega⟩ = H ⟨i.val, by omega⟩ ⟨a + k.val, by omega⟩ from rfl)
  have right : ((D.submatrix Sum.inr id).submatrix id (sᶜ.orderEmbOfFin hsc)) =
      (Matrix.of (fun i k : Fin (a + u) =>
        H⁻¹ (boundaryIndex a j u i) ⟨j + k.val, by omega⟩)).transpose := by
    ext i k; simpa [D, e, complement] using (show H⁻¹ (boundaryIndex a j u k) (Fin.natAdd j i) = H⁻¹ (boundaryIndex a j u k) ⟨j + i.val, by omega⟩ from rfl)
  rw [left, right, Matrix.det_transpose] at jacobi
  exact jacobi

/-- Coefficients reversed at a specified common support degree, with zero outside it. -/
def reverseCoeffs (N : ℕ) (c : ℕ → ℤ) (h : ℕ) : ℤ :=
  if h ≤ N then c (N - h) else 0

private theorem bezout_reverse_sum (N i j : ℕ) (hi : i < N) (hj : j < N)
    (c d : ℕ → ℤ) (cs : ∀ k, N < k → c k = 0) (ds : ∀ k, N < k → d k = 0) :
    -(∑ a ∈ range (j + 1),
      (c (i + j + 1 - a) * d a - d (i + j + 1 - a) * c a)) =
    ∑ b ∈ range (N - j),
      (reverseCoeffs N c ((N - 1 - i) + (N - 1 - j) + 1 - b) * reverseCoeffs N d b -
       reverseCoeffs N d ((N - 1 - i) + (N - 1 - j) + 1 - b) * reverseCoeffs N c b) := by
  let f := fun a => c (i + j + 1 - a) * d a - d (i + j + 1 - a) * c a
  have total : ∑ a ∈ range (i + j + 2), f a = 0 := by
    have reflected := sum_range_reflect f (i + j + 2)
    have terms : (∑ a ∈ range (i + j + 2), f (i + j + 2 - 1 - a)) =
        -(∑ a ∈ range (i + j + 2), f a) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro a ha
      have ha' := mem_range.mp ha
      dsimp [f]
      rw [show i + j + 1 - (i + j + 1 - a) = a by omega]
      ring
    rw [terms] at reflected
    omega
  have tail : -(∑ a ∈ range (j + 1), f a) =
      ∑ a ∈ range (i + 1), f (j + 1 + a) := by
    rw [show i + j + 2 = (j + 1) + (i + 1) by omega, sum_range_add] at total
    omega
  rw [tail]
  let g := fun b =>
    reverseCoeffs N c ((N - 1 - i) + (N - 1 - j) + 1 - b) * reverseCoeffs N d b -
    reverseCoeffs N d ((N - 1 - i) + (N - 1 - j) + 1 - b) * reverseCoeffs N c b
  change _ = ∑ b ∈ range (N - j), g b
  have bound (a : ℕ) (ha : f (j + 1 + a) ≠ 0) : j + 1 + a ≤ N := by
    by_contra hn
    have hh : N < j + 1 + a := by omega
    exact ha (by simp [f, cs _ hh, ds _ hh])
  have equality (a : ℕ) (ha : a ≤ i) (hb : j + 1 + a ≤ N) :
      f (j + 1 + a) = g (N - j - 1 - a) := by
    have h₁ : N - j - 1 - a ≤ N := by omega
    have h₂ : (N - 1 - i) + (N - 1 - j) + 1 - (N - j - 1 - a) ≤ N := by omega
    dsimp [f, g, reverseCoeffs]
    simp only [if_pos h₂, if_pos h₁]
    rw [show N - ((N - 1 - i) + (N - 1 - j) + 1 - (N - j - 1 - a)) =
        i + j + 1 - (j + 1 + a) by omega,
      show N - (N - j - 1 - a) = j + 1 + a by omega]
  apply sum_bij_ne_zero (fun a _ _ => N - j - 1 - a)
  · intro a ha hn
    have := bound a hn
    rw [mem_range]; omega
  · intro a ha hn b hb hm he
    have := bound a hn
    have := bound b hm
    omega
  · intro b hb hn
    have hb' := mem_range.mp hb
    have depth : (N - 1 - i) + (N - 1 - j) + 1 - b ≤ N := by
      by_contra hd
      exact hn (by simp only [g, reverseCoeffs, if_neg hd, zero_mul, sub_self])
    let a := N - j - 1 - b
    have ha : a ≤ i := by dsimp [a]; omega
    have hbound : j + 1 + a ≤ N := by dsimp [a]; omega
    have he : N - j - 1 - a = b := by dsimp [a]; omega
    refine ⟨a, mem_range.mpr (by omega), ?_, he⟩
    rw [equality a ha hbound, he]
    exact hn
  · intro a ha hn
    exact equality a (by have := mem_range.mp ha; omega) (bound a hn)

/-- Fixed boundary matrix. Its low rows use the low/high mixed Bezout formula;
its high rows use the common-degree reversed Bezout formula. -/
noncomputable def boundaryMatrix (a j u : ℕ) (c d : ℕ → ℤ) :
    Matrix (Fin (a + u)) (Fin (a + u)) ℤ := Matrix.of fun i k =>
  if i.val < a then
    -∑ v ∈ range (i.val + 1),
      if k.val + i.val + 1 ≤ a + u + v then
        reverseCoeffs (j + (a + u)) c (a + u + v - (k.val + i.val + 1)) * d v -
        reverseCoeffs (j + (a + u)) d (a + u + v - (k.val + i.val + 1)) * c v
      else 0
  else
    ∑ v ∈ range (a + u - k.val),
      (reverseCoeffs (j + (a + u)) c
        ((a + u - 1 - i.val) + (a + u - 1 - k.val) + 1 - v) *
          reverseCoeffs (j + (a + u)) d v -
       reverseCoeffs (j + (a + u)) d
        ((a + u - 1 - i.val) + (a + u - 1 - k.val) + 1 - v) *
          reverseCoeffs (j + (a + u)) c v)

private theorem inverse_entries (N : ℕ) (hN : 0 < N) (μ c d : ℕ → ℤ)
    (hc : c N = 1) (cs : ∀ k, N < k → c k = 0) (ds : ∀ k, N ≤ k → d k = 0)
    (orthogonal : ∀ t < N, ∑ r ∈ range (N + 1), c r * μ (r + t) = 0)
    (previous : ∀ t < N, ∑ r ∈ range N, d r * μ (r + t) =
      if t = N - 1 then -1 else 0)
    (unit : IsUnit (Matrix.of fun i k : Fin N => μ (i.val + k.val)).det) :
    ∀ i k : Fin N, (Matrix.of fun i k : Fin N => μ (i.val + k.val))⁻¹ i k =
      -∑ v ∈ range (k.val + 1),
        (c (i.val + k.val + 1 - v) * d v - d (i.val + k.val + 1 - v) * c v) := by
  cases N with
  | zero => omega
  | succ n =>
    exact MetallicHankelBoundaryPolynomials.hankel_inverse_bezout μ n c d hc cs ds
      orthogonal previous unit

/-- An actual shifted Hankel determinant equals its ordered fixed-dimensional boundary
Bezout determinant, with the exact sign. The empty target is included. -/
private theorem moment_boundary (a j u : ℕ) (hN : 0 < j + (a + u))
    (μ c d : ℕ → ℤ)
    (hc : c (j + (a + u)) = 1)
    (cs : ∀ k, j + (a + u) < k → c k = 0)
    (ds : ∀ k, j + (a + u) ≤ k → d k = 0)
    (orthogonal : ∀ t < j + (a + u),
      ∑ r ∈ range (j + (a + u) + 1), c r * μ (r + t) = 0)
    (previous : ∀ t < j + (a + u),
      ∑ r ∈ range (j + (a + u)), d r * μ (r + t) =
        if t = j + (a + u) - 1 then -1 else 0)
    (unit : IsUnit (Matrix.of fun i k : Fin (j + (a + u)) => μ (i.val + k.val)).det) :
    (Matrix.of fun i k : Fin j => μ (a + i.val + k.val)).det =
      (-1 : ℤ) ^ (a * j) *
        (Matrix.of fun i k : Fin (j + (a + u)) => μ (i.val + k.val)).det *
        (boundaryMatrix a j u c d).det := by
  classical
  let N := j + (a + u)
  let H : Matrix (Fin N) (Fin N) ℤ := Matrix.of fun i k => μ (i.val + k.val)
  have inv : ∀ i k : Fin N, H⁻¹ i k =
      -∑ v ∈ range (k.val + 1),
        (c (i.val + k.val + 1 - v) * d v - d (i.val + k.val + 1 - v) * c v) :=
    inverse_entries N hN μ c d hc cs ds orthogonal previous unit
  have symm : H.IsSymm := by ext i k; simp [H, Nat.add_comm]
  have entries (i k : Fin (a + u)) :
      H⁻¹ (boundaryIndex a j u i) ⟨j + k.val, by dsimp [N]; omega⟩ =
        boundaryMatrix a j u c d i k := by
    dsimp [boundaryMatrix, Matrix.of_apply]
    split_ifs with hia
    · rw [← symm.inv.apply, inv]
      simp only [boundaryIndex, if_pos hia, Fin.val_mk]
      congr 1
      apply sum_congr rfl
      intro v hv
      have hv' := mem_range.mp hv
      by_cases hd : k.val + i.val + 1 ≤ a + u + v
      · rw [if_pos hd]
        have depth : a + u + v - (k.val + i.val + 1) ≤ j + (a + u) := by omega
        simp only [reverseCoeffs, if_pos depth]
        rw [show j + (a + u) - (a + u + v - (k.val + i.val + 1)) =
          j + k.val + i.val + 1 - v by omega]
      · rw [if_neg hd]
        have hh : j + (a + u) < j + k.val + i.val + 1 - v := by omega
        rw [cs _ hh, ds _ (Nat.le_of_lt hh)]
        ring
    · rw [inv]
      have hr := bezout_reverse_sum N (j + i.val) (j + k.val)
        (by dsimp [N]; omega) (by dsimp [N]; omega) c d cs (fun v hv => ds v (by omega))
      simpa [boundaryIndex, hia, N, show j + (a + u) - (j + k.val) = a + u - k.val by omega,
        show j + (a + u) - 1 - (j + i.val) = a + u - 1 - i.val by omega,
        show j + (a + u) - 1 - (j + k.val) = a + u - 1 - k.val by omega] using hr
  have hb := shifted_minor a j u H unit
  have ht : (Matrix.of fun i k : Fin j =>
      H ⟨i.val, by dsimp [N]; omega⟩ ⟨a + k.val, by dsimp [N]; omega⟩) =
      Matrix.of (fun i k : Fin j => μ (a + i.val + k.val)) := by
    ext i k; dsimp [H]; congr 1; omega
  rw [ht] at hb
  have hm : (Matrix.of fun i k : Fin (a + u) =>
      H⁻¹ (boundaryIndex a j u i) ⟨j + k.val, by dsimp [N]; omega⟩) =
      boundaryMatrix a j u c d := by ext i k; exact entries i k
  rw [hm] at hb
  exact hb

/-- The ordered complementary boundary formula for the actual shiftedHankel definition.
Taking base=n+1 uses exactly the normal moment hypotheses supplied by normal_family. -/
theorem shifted_hankel_boundary (Φ : PowerSeries ℤ) (base a j u : ℕ)
    (hN : 0 < j + (a + u)) (c d : ℕ → ℤ)
    (hc : c (j + (a + u)) = 1)
    (cs : ∀ k, j + (a + u) < k → c k = 0)
    (ds : ∀ k, j + (a + u) ≤ k → d k = 0)
    (orthogonal : ∀ t < j + (a + u),
      ∑ r ∈ range (j + (a + u) + 1), c r * PowerSeries.coeff (base + r + t) Φ = 0)
    (previous : ∀ t < j + (a + u),
      ∑ r ∈ range (j + (a + u)), d r * PowerSeries.coeff (base + r + t) Φ =
        if t = j + (a + u) - 1 then -1 else 0)
    (unit : IsUnit (MetallicHankelDefs.shiftedHankel Φ base (j + (a + u)))) :
    MetallicHankelDefs.shiftedHankel Φ (base + a) j =
      (-1 : ℤ) ^ (a * j) * MetallicHankelDefs.shiftedHankel Φ base (j + (a + u)) *
        (boundaryMatrix a j u c d).det := by
  have h := moment_boundary a j u hN (fun t => PowerSeries.coeff (base + t) Φ) c d hc cs ds
    (by simpa only [Nat.add_assoc] using orthogonal)
    (by simpa only [Nat.add_assoc] using previous)
    (by simpa only [MetallicHankelDefs.shiftedHankel, Nat.add_assoc] using unit)
  simpa only [MetallicHankelDefs.shiftedHankel, Nat.add_assoc] using h

#print axioms shifted_minor
#print axioms shifted_hankel_boundary

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelComplementaryMinor
