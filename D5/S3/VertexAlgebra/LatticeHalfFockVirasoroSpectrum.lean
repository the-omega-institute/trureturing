/- GID: D5/S3/VertexAlgebra/LatticeHalfFockVirasoroSpectrum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockVirasoroSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual half-integer lattice currents, finite normal sums and Virasoro fields. -/

/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Additional actual half-integer matrix implementation copyright (c) 2026.
Released under Apache 2.0.
Finite support, contraction and induction architecture adapted from
VirasoroProject 5ff4245383b2cdd4eea7a0524bc1274c32041eb4 through the completed
trureturing PolynomialFock sources at bfd9ff0f15397a4fb933f36d701a60d325d84b08.
Actual multicolour half-index operators and their proofs are retained from the
completed half-Fock producer; see notes/NOTICE.md and DeclarationMapping.json.
DN math/9808088v1, section 3.2, pp.12--14; rank/16 on p.19, proof of 3.13(3),
attributed there to FLM. BK math/0402315v1 (4.4), pp.10--13 (4.23)--(4.38).
-/
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentNormal
import Mathlib.Data.Finsupp.Weight

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockBoundary
open scoped BigOperators
noncomputable section

def term (m j : ℤ) : ℂ :=
  ((j : ℂ)+1/2) * ((m : ℂ)+(j : ℂ)+1/2) *
    ((if 0 ≤ j then (1 : ℂ) else 0) - (if 0 ≤ m+j then (1 : ℂ) else 0))

theorem term_finite (m : ℤ) : Function.HasFiniteSupport (term m) := by
  apply (Set.finite_Icc (min 0 (-m)) (max 0 (-m))).subset
  intro j hj
  by_contra h
  simp only [Set.mem_Icc, not_and_or, not_le] at h
  rcases h with h | h
  · have hjneg : ¬ 0 ≤ j := by omega
    have hmjneg : ¬ 0 ≤ m+j := by omega
    exact hj (by simp [term, hjneg, hmjneg])
  · have hjpos : 0 ≤ j := by omega
    have hmjpos : 0 ≤ m+j := by omega
    exact hj (by simp [term, hjpos, hmjpos])

private theorem sum_Ico_id (a b : ℤ) (hab : a ≤ b) :
    ∑ x ∈ Finset.Ico a b, (x : ℂ) = ((a : ℂ)+b-1)*((b : ℂ)-a)/2 := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ b hb ih =>
    have hins : Finset.Ico a (b+1) = insert b (Finset.Ico a b) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hins, Finset.sum_insert (by simp only [Finset.mem_Ico]; omega), ih]
    push_cast; ring

private theorem sum_Ico_sq (a b : ℤ) (hab : a ≤ b) :
    ∑ x ∈ Finset.Ico a b, (x : ℂ)^2 =
      ((b : ℂ)-1)*(b : ℂ)*(2*(b : ℂ)-1)/6 -
      ((a : ℂ)-1)*(a : ℂ)*(2*(a : ℂ)-1)/6 := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ b hb ih =>
    have hins : Finset.Ico a (b+1) = insert b (Finset.Ico a b) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hins, Finset.sum_insert (by simp only [Finset.mem_Ico]; omega), ih]
    push_cast; ring

private theorem sum_Ico_quadratic (a b : ℤ) (hab : a ≤ b) (c₂ c₁ c₀ : ℂ) :
    ∑ x ∈ Finset.Ico a b, (c₂*(x : ℂ)^2+c₁*(x : ℂ)+c₀) =
      c₂*(((b : ℂ)-1)*(b : ℂ)*(2*(b : ℂ)-1)/6 -
        ((a : ℂ)-1)*(a : ℂ)*(2*(a : ℂ)-1)/6) +
      c₁*(((a : ℂ)+b-1)*((b : ℂ)-a)/2) + c₀*((b : ℂ)-a) := by
  have hc : ((Finset.Ico a b).card : ℂ) = (b : ℂ)-a := by
    rw [Int.card_Ico]
    exact_mod_cast Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ b-a)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hc,
    sum_Ico_id a b hab, sum_Ico_sq a b hab]
  ring

theorem term_sum (m : ℤ) : ∑ᶠ j : ℤ, term m j = (2*(m : ℂ)^3+(m : ℂ))/12 := by
  rcases le_total 0 m with hm | hm
  · rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.Ico (-m) 0) ?_]
    · rw [Finset.sum_congr rfl
        (g := fun j : ℤ => (-1 : ℂ)*(j : ℂ)^2+(-(m : ℂ)-1)*(j : ℂ)+(-(m : ℂ)/2-1/4)) ?_,
        sum_Ico_quadratic (-m) 0 (by omega)]
      · push_cast; ring
      · intro j hj
        simp only [Finset.mem_Ico] at hj
        simp only [term, if_neg (show ¬ 0 ≤ j by omega), if_pos (show 0 ≤ m+j by omega)]
        ring
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_Ico]
      by_contra h
      have ho : j < -m ∨ 0 ≤ j := by omega
      rcases ho with h | h
      · exact hj (by simp [term, show ¬ 0 ≤ j by omega, show ¬ 0 ≤ m+j by omega])
      · exact hj (by simp [term, h, show 0 ≤ m+j by omega])
  · rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.Ico 0 (-m)) ?_]
    · rw [Finset.sum_congr rfl
        (g := fun j : ℤ => (1 : ℂ)*(j : ℂ)^2+((m : ℂ)+1)*(j : ℂ)+((m : ℂ)/2+1/4)) ?_,
        sum_Ico_quadratic 0 (-m) (by omega)]
      · push_cast; ring
      · intro j hj
        simp only [Finset.mem_Ico] at hj
        simp only [term, if_pos (show 0 ≤ j by omega), if_neg (show ¬ 0 ≤ m+j by omega)]
        ring
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_Ico]
      by_contra h
      have ho : j < 0 ∨ -m ≤ j := by omega
      rcases ho with h | h
      · exact hj (by simp [term, show ¬ 0 ≤ j by omega, show ¬ 0 ≤ m+j by omega])
      · exact hj (by simp [term, show 0 ≤ j by omega, show 0 ≤ m+j by omega])

private theorem half_sum_linear (m : ℕ) :
    (∑ k ∈ Finset.range m, ((k : ℂ)+1/2)) = (m : ℂ)^2/2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

private theorem natural_boundary (m : ℕ) :
    (1/2 : ℂ)*∑ k ∈ Finset.range m, ((k : ℂ)+1/2)*((m : ℂ)-(k : ℂ)-1/2) =
      (2*(m : ℂ)^3+(m : ℂ))/24 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hs : (∑ k ∈ Finset.range m,
        ((k : ℂ)+1/2)*(((m+1 : ℕ) : ℂ)-(k : ℂ)-1/2)) =
        (∑ k ∈ Finset.range m, ((k : ℂ)+1/2)*((m : ℂ)-(k : ℂ)-1/2))+(m : ℂ)^2/2 := by
      rw [← half_sum_linear, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      push_cast; ring
    rw [hs]
    push_cast at ih ⊢
    linear_combination ih

end
end D5.S3.VertexAlgebra.LatticeHalfFockBoundary

namespace D5.S3.VertexAlgebra.LatticeHalfFock
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration MvPolynomial
open LatticeActualAnnihilation
open scoped BigOperators TensorProduct
noncomputable section

def bracket (D : LatticeData) (A B : Module.End ℂ (Oscillator D)) := A*B-B*A

private theorem normalPair_boundary (D : LatticeData) (i l : Fin D.rank) (j k : ℤ) :
    normalPair D i l j k = current D i j * current D l k -
      (if 0 ≤ j ∧ j+k+1 = 0 then frequency j*(D.G i l : ℂ) else 0) • 1 := by
  by_cases hj : j < 0
  · simp [normalPair, hj, show ¬ 0 ≤ j by omega]
  · rw [normalPair, if_neg hj]
    have h := current_heisenberg D i l j k
    have hp : 0 ≤ j := by omega
    simp only [hp, true_and]
    exact eq_sub_iff_add_eq.mpr (by
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm)

private theorem rawL_product_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (m j k : ℤ) (i l : Fin D.rank) :
    bracket D (rawL D H m) (current D i j * current D l k) =
      -frequency k • (current D i j * current D l (m+k)) +
      -frequency j • (current D i (m+j) * current D l k) := by
  have expand : bracket D (rawL D H m) (current D i j * current D l k) =
      current D i j * bracket D (rawL D H m) (current D l k) +
      bracket D (rawL D H m) (current D i j) * current D l k := by
    unfold bracket
    apply LinearMap.ext
    intro p
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, map_sub, map_add]
    abel
  rw [expand]
  change _ * (rawL D H m * current D l k - current D l k * rawL D H m) +
    (rawL D H m * current D i j - current D i j * rawL D H m) * _ = _
  rw [rawL_current_commutator D H hHG hGH, rawL_current_commutator D H hHG hGH]
  simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

private theorem rawL_pair_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (m n j : ℤ) (i l : Fin D.rank) :
    bracket D (rawL D H m) (normalPair D i l j (n-j-1)) =
      -frequency (n-j-1) • normalPair D i l j (m+n-j-1) +
      -frequency j • normalPair D i l (m+j) (n-j-1) +
      (if m+n = 0 then LatticeHalfFockBoundary.term m j*(D.G i l : ℂ) else 0) • 1 := by
  have first : bracket D (rawL D H m) (normalPair D i l j (n-j-1)) =
      bracket D (rawL D H m) (current D i j * current D l (n-j-1)) := by
    rw [normalPair_boundary]
    simp [bracket, mul_sub, sub_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  rw [first, rawL_product_commutator D H hHG hGH,
    show m+(n-j-1) = m+n-j-1 by omega,
    normalPair_boundary D i l j (m+n-j-1),
    normalPair_boundary D i l (m+j) (n-j-1)]
  by_cases hmn : m+n = 0
  · obtain rfl : n = -m := by omega
    simp only [LatticeHalfFockBoundary.term, frequency]
    push_cast
    match_scalars
    · ring
    · ring
    · split_ifs <;> first | (exfalso; omega) | ring
  · have h₁ : ¬ (0 ≤ j ∧ j+(m+n-j-1)+1 = 0) := by omega
    have h₂ : ¬ (0 ≤ m+j ∧ (m+j)+(n-j-1)+1 = 0) := by omega
    simp only [hmn, h₁, h₂, if_false, zero_smul, sub_zero, add_zero]

private theorem shifted_pair_finite (D : LatticeData) (i l : Fin D.rank)
    (m n : ℤ) (p : Oscillator D) :
    Function.HasFiniteSupport (fun j : ℤ => normalPair D i l (m+j) (n-j-1) p) := by
  have h := (normalPair_finite D i l (m+n) p).fun_comp_of_injective
    (g := fun j : ℤ => m+j) (fun _ _ h => add_left_cancel h)
  simpa only [show ∀ j : ℤ, m+n-(m+j)-1 = n-j-1 by intro j; omega] using h

private theorem normal_pair_sum (D : LatticeData) (i l : Fin D.rank) (m n : ℤ)
    (p : Oscillator D) :
    ∑ᶠ j : ℤ, (-frequency (n-j-1) • normalPair D i l j (m+n-j-1) p +
      -frequency j • normalPair D i l (m+j) (n-j-1) p) =
      ((m : ℂ)-(n : ℂ)) • normalSum D i l (m+n) p := by
  have hf : Function.HasFiniteSupport (fun j : ℤ =>
      -frequency (n-j-1) • normalPair D i l j (m+n-j-1) p) := by
    simpa only [Pi.smul_def'] using Function.HasFiniteSupport.smul_right
      (fun j : ℤ => -frequency (n-j-1)) (normalPair_finite D i l (m+n) p)
  have hg : Function.HasFiniteSupport (fun j : ℤ =>
      -frequency j • normalPair D i l (m+j) (n-j-1) p) := by
    simpa only [Pi.smul_def'] using Function.HasFiniteSupport.smul_right
      (fun j : ℤ => -frequency j) (shifted_pair_finite D i l m n p)
  have changevar : (∑ᶠ j : ℤ, -frequency j • normalPair D i l (m+j) (n-j-1) p) =
      ∑ᶠ j : ℤ, ((m : ℂ)-frequency j) • normalPair D i l j (m+n-j-1) p := by
    rw [← finsum_comp_equiv (Equiv.subRight m)]
    apply finsum_congr
    intro j
    simp only [Equiv.subRight_apply]
    rw [show m+(j-m) = j by omega, show n-(j-m)-1 = m+n-j-1 by omega]
    congr 1
    simp only [frequency, Int.cast_sub]; ring
  rw [finsum_add_distrib hf hg, changevar]
  have hs : Function.HasFiniteSupport (fun j : ℤ =>
      ((m : ℂ)-frequency j) • normalPair D i l j (m+n-j-1) p) := by
    simpa only [Pi.smul_def'] using Function.HasFiniteSupport.smul_right
      (fun j : ℤ => (m : ℂ)-frequency j) (normalPair_finite D i l (m+n) p)
  rw [← finsum_add_distrib hf hs]
  calc
    _ = ∑ᶠ j : ℤ, ((m : ℂ)-(n : ℂ)) • normalPair D i l j (m+n-j-1) p := by
      apply finsum_congr
      intro j
      rw [← add_smul]
      congr 1
      simp only [frequency, Int.cast_sub, Int.cast_one]; ring
    _ = _ := (smul_finsum' _ (normalPair_finite D i l (m+n) p)).symm

private theorem rawL_normalSum_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (m n : ℤ) (i l : Fin D.rank) :
    bracket D (rawL D H m) (normalSum D i l n) =
      ((m : ℂ)-(n : ℂ)) • normalSum D i l (m+n) +
      (if m+n = 0 then ((2*(m : ℂ)^3+(m : ℂ))/12)*(D.G i l : ℂ) else 0) • 1 := by
  apply LinearMap.ext
  intro p
  change bracket D (rawL D H m) (normalSum D i l n) p =
    ((m : ℂ)-(n : ℂ)) • normalSum D i l (m+n) p +
      (if m+n = 0 then ((2*(m : ℂ)^3+(m : ℂ))/12)*(D.G i l : ℂ) else 0) • p
  have hNO : Function.HasFiniteSupport (fun j : ℤ =>
      -frequency (n-j-1) • normalPair D i l j (m+n-j-1) p +
      -frequency j • normalPair D i l (m+j) (n-j-1) p) :=
    by
      apply Function.HasFiniteSupport.add
      · simpa only [Pi.smul_def'] using Function.HasFiniteSupport.smul_right
          (fun j : ℤ => -frequency (n-j-1)) (normalPair_finite D i l (m+n) p)
      · simpa only [Pi.smul_def'] using Function.HasFiniteSupport.smul_right
          (fun j : ℤ => -frequency j) (shifted_pair_finite D i l m n p)
  have hCC : Function.HasFiniteSupport (fun j : ℤ =>
      (if m+n = 0 then LatticeHalfFockBoundary.term m j*(D.G i l : ℂ) else 0) • p) := by
    by_cases h : m+n = 0
    · simp only [h, if_true]
      simpa only [Pi.smul_def', Pi.mul_def] using
        ((LatticeHalfFockBoundary.term_finite m).mul_left (fun _ => (D.G i l : ℂ))).smul_left (fun _ => p)
    · simp only [h, if_false, zero_smul]
      exact Function.hasFiniteSupport_fun_zero
  have expand : bracket D (rawL D H m) (normalSum D i l n) p =
      ∑ᶠ j : ℤ, bracket D (rawL D H m) (normalPair D i l j (n-j-1)) p := by
    change rawL D H m (∑ᶠ j : ℤ, normalPair D i l j (n-j-1) p) -
      (∑ᶠ j : ℤ, normalPair D i l j (n-j-1) (rawL D H m p)) = _
    rw [map_finsum _ (normalPair_finite D i l n p),
      ← finsum_sub_distrib ((normalPair_finite D i l n p).fun_comp (map_zero (rawL D H m)))
        (normalPair_finite D i l n (rawL D H m p))]
    rfl
  rw [expand]
  have pair_apply : ∀ j : ℤ,
      bracket D (rawL D H m) (normalPair D i l j (n-j-1)) p =
        (-frequency (n-j-1) • normalPair D i l j (m+n-j-1) p +
          -frequency j • normalPair D i l (m+j) (n-j-1) p) +
          (if m+n = 0 then LatticeHalfFockBoundary.term m j*(D.G i l : ℂ) else 0) • p := by
    intro j
    exact congrArg (fun A : Module.End ℂ (Oscillator D) => A p)
      (rawL_pair_commutator D H hHG hGH m n j i l)
  rw [finsum_congr pair_apply, finsum_add_distrib hNO hCC, normal_pair_sum]
  congr 1
  by_cases h : m+n = 0
  · simp only [h, if_true]
    have hb : Function.HasFiniteSupport
        (fun j : ℤ => LatticeHalfFockBoundary.term m j*(D.G i l : ℂ)) := by
      simpa only [Pi.mul_def] using
        (LatticeHalfFockBoundary.term_finite m).mul_left (fun _ => (D.G i l : ℂ))
    calc
      _ = (∑ᶠ j : ℤ, LatticeHalfFockBoundary.term m j*(D.G i l : ℂ)) • p :=
        (finsum_smul' hb p).symm
      _ = _ := congrArg (fun c : ℂ => c • p)
        ((finsum_mul' (LatticeHalfFockBoundary.term m) (D.G i l : ℂ)
          (LatticeHalfFockBoundary.term_finite m)).symm.trans
          (congrArg (fun c : ℂ => c*(D.G i l : ℂ)) (LatticeHalfFockBoundary.term_sum m)))
  · simp [h]

private theorem inverse_trace (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) :
    ∑ i : Fin D.rank, ∑ l : Fin D.rank, H i l*(D.G i l : ℂ) = (D.rank : ℂ) := by
  have row (i : Fin D.rank) : ∑ l, H i l*(D.G i l : ℂ) = 1 := by
    have h := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M i i) hHG
    simpa [Matrix.mul_apply, gramComplex, D.symmetric i] using h
  simp_rw [row]
  simp

theorem rawL_virasoro (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (m n : ℤ) :
    rawL D H m * rawL D H n - rawL D H n * rawL D H m =
      ((m : ℂ)-(n : ℂ)) • rawL D H (m+n) +
      (if m+n = 0 then (D.rank : ℂ)*(2*(m : ℂ)^3+(m : ℂ))/24 else 0) • 1 := by
  classical
  let leftBracket : Module.End ℂ (Oscillator D) →ₗ[ℂ] Module.End ℂ (Oscillator D) :=
    -rightBracket D (rawL D H m)
  have he (A : Module.End ℂ (Oscillator D)) : leftBracket A = bracket D (rawL D H m) A := by
    change -(A*rawL D H m-rawL D H m*A) = _
    unfold bracket; abel
  change bracket D (rawL D H m) (rawL D H n) = _
  rw [← he (rawL D H n)]
  rw [rawL, map_smul]
  simp_rw [map_sum, map_smul, he, rawL_normalSum_commutator D H hHG hGH,
    smul_add, Finset.sum_add_distrib]
  rw [smul_add]
  congr 1
  · simp_rw [smul_comm (H _ _) ((m : ℂ)-(n : ℂ)), ← Finset.smul_sum]
    rw [smul_comm]
    rfl
  · by_cases h : m+n = 0
    · simp only [h, if_true, smul_smul]
      simp_rw [show ∀ i l : Fin D.rank,
        H i l*(((2*(m : ℂ)^3+(m : ℂ))/12)*(D.G i l : ℂ)) =
        ((2*(m : ℂ)^3+(m : ℂ))/12)*(H i l*(D.G i l : ℂ)) by intros; ring]
      simp_rw [← Finset.sum_smul, ← Finset.mul_sum]
      rw [inverse_trace D H hHG, smul_smul]
      congr 1
      ring
    · simp [h]

theorem positive_ground_boundary (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (m : ℕ) :
    rawL D H m (rawL D H (-(m : ℤ)) (1 : Oscillator D)) =
      ((D.rank : ℂ)/2*∑ k ∈ Finset.range m,
        ((k : ℂ)+1/2)*((m : ℂ)-(k : ℂ)-1/2)) • 1 := by
  have h := congrArg (fun A : Module.End ℂ (Oscillator D) => A 1)
    (rawL_virasoro D H hHG hGH (m : ℤ) (-(m : ℤ)))
  have hz : (m : ℤ)+-(m : ℤ) = 0 := by omega
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply, hz, if_true, Int.cast_natCast,
    rawL_ground_nonnegative D H (m : ℤ) (by omega),
    rawL_ground_nonnegative D H 0 (by omega), map_zero, sub_zero, smul_zero, zero_add] at h
  rw [h]
  congr 1
  have ha := LatticeHalfFockBoundary.natural_boundary m
  linear_combination -(D.rank : ℂ)*ha

theorem L_virasoro (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (m n : ℤ) :
    L D H m * L D H n - L D H n * L D H m =
      ((m : ℂ)-(n : ℂ)) • L D H (m+n) +
      (if m+n = 0 then ((D.rank : ℂ)/12)*((m : ℂ)^3-(m : ℂ)) else 0) • 1 := by
  have comm : L D H m * L D H n - L D H n * L D H m =
      rawL D H m * rawL D H n - rawL D H n * rawL D H m := by
    apply LinearMap.ext
    intro p
    simp only [L, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul, smul_add, smul_smul]
    rw [mul_comm (if m = 0 then (D.rank : ℂ)/16 else 0) (if n = 0 then (D.rank : ℂ)/16 else 0)]
    abel
  rw [comm, rawL_virasoro D H hHG hGH, L, smul_add, smul_smul]
  by_cases h : m+n = 0
  · have hn : (n : ℂ) = -(m : ℂ) := by exact_mod_cast (show n = -m by omega)
    simp only [h, if_true, hn]
    rw [add_assoc, ← add_smul]
    congr 2
    ring
  · simp [h]

theorem shift_forced (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (h : ℂ)
    (hnorm : (rawL D H 1 * rawL D H (-1) - rawL D H (-1) * rawL D H 1)
      (1 : Oscillator D) = (2*h) • 1) : h = (D.rank : ℂ)/16 := by
  have he := congrArg (fun A : Module.End ℂ (Oscillator D) => A 1)
    (rawL_virasoro D H hHG hGH 1 (-1))
  norm_num [rawL_ground_nonnegative D H 0 (by omega)] at he
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at hnorm
  rw [he] at hnorm
  have hc := congrArg constantCoeff hnorm
  simp only [constantCoeff_smul, map_one, smul_eq_mul, mul_one] at hc
  linear_combination -hc/2

def energy (D : LatticeData) (d : Index D →₀ ℕ) : ℂ :=
  Finsupp.weight (fun x : Index D => (x.2 : ℂ)+1/2) d

private theorem energy_sum (D : LatticeData) (d : Index D →₀ ℕ) :
    energy D d = ∑ x ∈ d.support, (d x : ℂ)*((x.2 : ℂ)+1/2) := by
  simp [energy, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro x hx
  ring

private theorem L_zero_X_mul (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : Index D) (p : Oscillator D) :
    L D H 0 (X x*p) = X x*L D H 0 p + ((x.2 : ℂ)+1/2) • (X x*p) := by
  have h := congrArg (fun A : Module.End ℂ (Oscillator D) => A p)
    (L_current_commutator D H hHG hGH x.1 0 (-(x.2 : ℤ)-1))
  simp only [current_negative, zero_add, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, LinearMap.mulLeft_apply] at h
  have hf : -frequency (-(x.2 : ℤ)-1) = (x.2 : ℂ)+1/2 := by
    simp only [frequency, Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one]; ring
  rw [hf] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

private theorem L_zero_X_pow_mul (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : Index D) (e : ℕ) (p : Oscillator D) (E : ℂ) (hp : L D H 0 p = E • p) :
    L D H 0 (X x^e*p) = (E+(e : ℂ)*((x.2 : ℂ)+1/2)) • (X x^e*p) := by
  induction e with
  | zero => simpa using hp
  | succ e ih =>
    have hm : X x^(e+1)*p = X x*(X x^e*p) := by rw [pow_succ']; ring
    rw [hm, L_zero_X_mul D H hHG hGH, ih, mul_smul_comm, ← add_smul]
    congr 1
    push_cast; ring

private theorem L_zero_monomial (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (d : Index D →₀ ℕ) :
    L D H 0 (monomial d (1 : ℂ)) =
      ((D.rank : ℂ)/16+energy D d) • monomial d (1 : ℂ) := by
  classical
  induction d using Finsupp.induction with
  | zero => simpa [energy] using L_ground_zero D H
  | single_add x e d _ _ ih =>
    have he : energy D (Finsupp.single x e+d) =
        (e : ℂ)*((x.2 : ℂ)+1/2)+energy D d := by
      rw [energy, map_add, Finsupp.weight_single]
      simp [energy, nsmul_eq_mul]
      ring
    have hm : monomial (Finsupp.single x e+d) (1 : ℂ) =
        X x^e*monomial d (1 : ℂ) := by
      rw [X_pow_eq_monomial, monomial_mul]; simp
    rw [hm, he]
    have hc : (D.rank : ℂ)/16+((e : ℂ)*((x.2 : ℂ)+1/2)+energy D d) =
        ((D.rank : ℂ)/16+energy D d)+(e : ℂ)*((x.2 : ℂ)+1/2) := by ring
    rw [hc]
    exact L_zero_X_pow_mul D H hHG hGH x e (monomial d 1) _ ih

theorem L_zero_monomial_coeff (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (d : Index D →₀ ℕ) (c : ℂ) :
    L D H 0 (monomial d c) =
      ((D.rank : ℂ)/16+∑ x ∈ d.support, (d x : ℂ)*((x.2 : ℂ)+1/2)) • monomial d c := by
  have hm : monomial d c = c • monomial d (1 : ℂ) := by
    simp only [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, L_zero_monomial D H hHG hGH, energy_sum, smul_comm]

end
end D5.S3.VertexAlgebra.LatticeHalfFock
