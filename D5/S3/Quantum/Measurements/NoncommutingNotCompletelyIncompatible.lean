/- GID: D5/S3/Quantum/Measurements/NoncommutingNotCompletelyIncompatible
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/NoncommutingNotCompletelyIncompatible
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Nontrivial coordinate projectors can all fail to commute without COINC for d >= 4. -/

/-
proof_shape: result: bind-only
escape_witness: none (the explicit reflection and integer parity calculations are normalization)
admission_basis: open-problem-resolution (#11785; Proved)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

namespace D5.S3.Quantum.Measurements.NoncommutingNotCompletelyIncompatible

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix

/-- The matrix of the orthogonal projector onto the indicated basis vectors. -/
def projector {d : ℕ} (b : (OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)))) (S : Finset (Fin d)) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => ∑ k ∈ S, b k i * star (b k j)

def NonCommutingProjectors {d : ℕ} (a b : (OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)))) : Prop :=
  ∀ S T : Finset (Fin d), S.Nonempty → S ≠ Finset.univ →
    T.Nonempty → T ≠ Finset.univ →
    projector a S * projector b T ≠ projector b T * projector a S

def CompletelyIncompatible {d : ℕ} (a b : (OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)))) : Prop :=
  ∀ S T : Finset (Fin d), S.card + T.card ≤ d →
    Submodule.span ℂ (a '' (↑S : Set (Fin d))) ⊓
      Submodule.span ℂ (b '' (↑T : Set (Fin d))) = ⊥

def claim : Prop := ∀ d : ℕ, 4 ≤ d → ∃ a b : (OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))),
  NonCommutingProjectors a b ∧ ¬ CompletelyIncompatible a b

theorem result : claim := by
  classical
  let weight {d : ℕ} (i : Fin d) : ℤ := if i.val = 0 then 1 else 2
  let mass {d : ℕ} (T : Finset (Fin d)) : ℤ := ∑ k ∈ T, weight k ^ 2
  let q (d : ℕ) : ℤ := mass (Finset.univ : Finset (Fin d))
  let wc {d : ℕ} (i : Fin d) : ℂ := (weight i : ℂ)
  let H (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
    1 - (2 / (q d : ℂ)) • Matrix.vecMulVec wc wc
  have weight_pos {d : ℕ} (i : Fin d) : 0 < weight i := by
    unfold weight
    split_ifs <;> norm_num
  have q_formula {d : ℕ} (hd : 0 < d) : q d = 4 * (d : ℤ) - 3 := by
    let o : Fin d := ⟨0, hd⟩
    have hw (i : Fin d) : weight i ^ 2 = 4 - if i = o then (3 : ℤ) else 0 := by
      by_cases h : i = o
      · subst i; simp [weight, o]
      · have hi : i.val ≠ 0 := by intro hh; apply h; exact Fin.ext hh
        simp [weight, hi, h]
    simp only [q, mass, hw, Finset.sum_sub_distrib]
    simp
    ring
  have mass_pos {d : ℕ} {T : Finset (Fin d)} (hT : T.Nonempty) : 0 < mass T := by
    exact Finset.sum_pos (fun i _ => sq_pos_of_pos (weight_pos i)) hT
  have mass_lt {d : ℕ} {T : Finset (Fin d)} (hT : T ≠ Finset.univ) : mass T < q d := by
    classical
    have hex : ∃ k : Fin d, k ∉ T := by
      by_contra h
      apply hT
      apply Finset.eq_univ_of_forall
      intro k
      by_contra hk
      exact h ⟨k, hk⟩
    obtain ⟨k, hk⟩ := hex
    exact Finset.sum_lt_sum_of_subset (Finset.subset_univ T) (Finset.mem_univ k) hk
      (sq_pos_of_pos (weight_pos k))
      (fun i _ _ => le_of_lt (sq_pos_of_pos (weight_pos i)))
  have wc_star {d : ℕ} (i : Fin d) : star (wc i) = wc i := by
    simp [wc]
  have sum_wc_sq (d : ℕ) : ∑ i : Fin d, wc i * wc i = (q d : ℂ) := by
    simp [q, mass, wc, pow_two, Int.cast_sum]
  have q_ne {d : ℕ} (hd : 0 < d) : (q d : ℂ) ≠ 0 := by
    have h : 0 < q d := mass_pos (Finset.univ_nonempty_iff.mpr ⟨⟨0, hd⟩⟩)
    exact_mod_cast ne_of_gt h
  have H_entry (d : ℕ) (i j : Fin d) :
      H d i j = (if i = j then 1 else 0) - (2 / (q d : ℂ)) * wc i * wc j := by
    simp [H, Matrix.one_apply, Matrix.vecMulVec_apply, mul_assoc]
  have H_symm (d : ℕ) (i j : Fin d) : H d i j = H d j i := by
    rw [H_entry, H_entry]
    simp only [eq_comm]
    ring
  have H_real (d : ℕ) (i j : Fin d) : star (H d i j) = H d i j := by
    simp [H_entry, wc_star]
  have H_square {d : ℕ} (hd : 0 < d) : H d * H d = 1 := by
    let R : Matrix (Fin d) (Fin d) ℂ := Matrix.vecMulVec wc wc
    have hR : R * R = (q d : ℂ) • R := by
      ext i j
      simp [R, Matrix.vecMulVec_mul_vecMulVec, dotProduct, sum_wc_sq]
    have hq := q_ne hd
    change (1 - (2 / (q d : ℂ)) • R) * (1 - (2 / (q d : ℂ)) • R) = 1
    simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hR, smul_smul]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
    ring
  let columns (d : ℕ) (j : Fin d) : (EuclideanSpace ℂ (Fin d)) := WithLp.toLp 2 (fun i => H d i j)
  have columns_orthonormal {d : ℕ} (hd : 0 < d) : Orthonormal ℂ (columns d) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hh := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) (H_square hd)
    rw [Matrix.mul_apply, Matrix.one_apply] at hh
    change (∑ k : Fin d, H d k j * star (H d k i)) = if i = j then 1 else 0
    simp_rw [H_real]
    convert hh using 1
    apply Finset.sum_congr rfl
    intro k _
    rw [H_symm d k i]
    ring
  let reflectedBasis {d : ℕ} (hd : 0 < d) : (OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) := by
    letI : NeZero d := ⟨ne_of_gt hd⟩
    let b := basisOfOrthonormalOfCardEqFinrank (columns_orthonormal hd) (by simp)
    have hb : (b : Fin d → (EuclideanSpace ℂ (Fin d))) = columns d :=
      coe_basisOfOrthonormalOfCardEqFinrank _ _
    exact b.toOrthonormalBasis (by rw [hb]; exact columns_orthonormal hd)
  have reflectedBasis_entry {d : ℕ} (hd : 0 < d) (k i : Fin d) :
      reflectedBasis hd k i = H d i k := by
    let : NeZero d := ⟨ne_of_gt hd⟩
    unfold reflectedBasis
    rw [Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]
  let indicator {d : ℕ} (T : Finset (Fin d)) (i : Fin d) : ℤ := if i ∈ T then 1 else 0
  let charge {d : ℕ} (T : Finset (Fin d)) (i j : Fin d) : ℤ :=
    2 * mass T - q d * (indicator T i + indicator T j)
  have charge_ne {d : ℕ} (hd : 0 < d) {T : Finset (Fin d)}
      (hne : T.Nonempty) (hproper : T ≠ Finset.univ) (i j : Fin d) : charge T i j ≠ 0 := by
    have hp := mass_pos hne
    have hl := mass_lt hproper
    have hq := q_formula hd
    unfold charge indicator
    split_ifs <;> omega
  have projector_reflected_entry {d : ℕ} (hd : 0 < d)
      (T : Finset (Fin d)) (i j : Fin d) (hij : i ≠ j) :
      projector (reflectedBasis hd) T i j =
        (2 * wc i * wc j / (q d : ℂ)^2) * (charge T i j : ℂ) := by
    classical
    have hq := q_ne hd
    have hsum : ∑ k ∈ T, wc k ^ 2 = (mass T : ℂ) := by
      simp [mass, wc, Int.cast_sum]
    have hterm (k : Fin d) : H d i k * H d j k =
        -(if k = i then (2 / (q d : ℂ)) * wc i * wc j else 0) -
         (if k = j then (2 / (q d : ℂ)) * wc i * wc j else 0) +
         (2 / (q d : ℂ))^2 * wc i * wc j * wc k^2 := by
      rw [H_entry, H_entry]
      by_cases hki : k = i
      · subst k; simp [hij, Ne.symm hij]; ring
      · by_cases hkj : k = j
        · subst k; simp [hij, Ne.symm hij]; ring
        · simp [hki, hkj, Ne.symm hki, Ne.symm hkj]; ring
    unfold projector
    simp_rw [reflectedBasis_entry, H_real, hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    simp only [Finset.sum_ite_eq', ← Finset.mul_sum, hsum]
    unfold charge indicator
    push_cast
    by_cases hi : i ∈ T <;> by_cases hj : j ∈ T <;> simp [hi, hj] <;> field_simp <;> ring
  have projector_reflected_offdiag_ne {d : ℕ} (hd : 0 < d)
      {T : Finset (Fin d)} (hne : T.Nonempty) (hproper : T ≠ Finset.univ)
      (i j : Fin d) (hij : i ≠ j) : projector (reflectedBasis hd) T i j ≠ 0 := by
    rw [projector_reflected_entry hd T i j hij]
    apply mul_ne_zero
    · apply div_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · norm_num
          · change (weight i : ℂ) ≠ 0
            exact_mod_cast ne_of_gt (weight_pos i)
        · change (weight j : ℂ) ≠ 0
          exact_mod_cast ne_of_gt (weight_pos j)
      · exact pow_ne_zero _ (q_ne hd)
    · exact_mod_cast charge_ne hd hne hproper i j
  have projector_standard {d : ℕ} (S : Finset (Fin d)) :
      projector (EuclideanSpace.basisFun (Fin d) ℂ) S =
        Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0) := by
    classical
    ext i j
    simp only [projector, EuclideanSpace.basisFun_apply, PiLp.single_apply,
      apply_ite star, star_one, star_zero, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst j
      simp
    · have hz (k : Fin d) : (if i = k then (1 : ℂ) else 0) *
          (if j = k then 1 else 0) = 0 := by
        by_cases hik : i = k
        · subst k; simp [Ne.symm hij]
        · simp [hik]
      simp [hz, hij]
  have all_noncommuting {d : ℕ} (hd : 0 < d) :
      NonCommutingProjectors (EuclideanSpace.basisFun (Fin d) ℂ) (reflectedBasis hd) := by
    classical
    intro S T hS hpS hT hpT heq
    obtain ⟨i, hi⟩ := hS
    have hex : ∃ j : Fin d, j ∉ S := by
      by_contra h
      apply hpS
      apply Finset.eq_univ_of_forall
      intro j
      by_contra hj
      exact h ⟨j, hj⟩
    obtain ⟨j, hj⟩ := hex
    have hij : i ≠ j := by intro h; subst j; exact hj hi
    have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) heq
    rw [projector_standard, Matrix.diagonal_mul, Matrix.mul_diagonal] at he
    simp only [if_pos hi, if_neg hj, one_mul, mul_zero] at he
    exact projector_reflected_offdiag_ne hd hT hpT i j hij he
  have not_coinc {d : ℕ} (hd : 4 ≤ d) :
      ¬ CompletelyIncompatible (EuclideanSpace.basisFun (Fin d) ℂ)
        (reflectedBasis (by omega : 0 < d)) := by
    classical
    let a : Fin d := ⟨0, by omega⟩
    let b : Fin d := ⟨1, by omega⟩
    have hab : a ≠ b := by intro h; have := congrArg Fin.val h; simp [a, b] at this
    let T : Finset (Fin d) := {a, b}
    let z : Fin d → ℂ := (2 : ℂ) • Pi.single a 1 - Pi.single b 1
    have hz_ne : z ≠ 0 := by
      intro h
      have he := congrFun h a
      simp [z, hab] at he
    have hdpos : 0 < d := by omega
    let v : (EuclideanSpace ℂ (Fin d)) := WithLp.toLp 2 z
    have hv_ne : v ≠ 0 := by
      intro h
      apply hz_ne
      exact congrArg WithLp.ofLp h
    have hvA : v ∈ Submodule.span ℂ ((EuclideanSpace.basisFun (Fin d) ℂ) ''
        (↑T : Set (Fin d))) := by
      have ha : EuclideanSpace.basisFun (Fin d) ℂ a ∈
          Submodule.span ℂ ((EuclideanSpace.basisFun (Fin d) ℂ) '' (↑T : Set (Fin d))) :=
        Submodule.subset_span ⟨a, by simp [T], rfl⟩
      have hb : EuclideanSpace.basisFun (Fin d) ℂ b ∈
          Submodule.span ℂ ((EuclideanSpace.basisFun (Fin d) ℂ) '' (↑T : Set (Fin d))) :=
        Submodule.subset_span ⟨b, by simp [T], rfl⟩
      have he : v = (2 : ℂ) • EuclideanSpace.basisFun (Fin d) ℂ a -
          EuclideanSpace.basisFun (Fin d) ℂ b := by
        ext i
        simp [v, z, EuclideanSpace.basisFun_apply, PiLp.single_apply, Pi.single_apply]
      rw [he]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ ha) hb
    have hvB : v ∈ Submodule.span ℂ ((reflectedBasis hdpos) '' (↑T : Set (Fin d))) := by
      have ha : reflectedBasis hdpos a ∈
          Submodule.span ℂ ((reflectedBasis hdpos) '' (↑T : Set (Fin d))) :=
        Submodule.subset_span ⟨a, by simp [T], rfl⟩
      have hb : reflectedBasis hdpos b ∈
          Submodule.span ℂ ((reflectedBasis hdpos) '' (↑T : Set (Fin d))) :=
        Submodule.subset_span ⟨b, by simp [T], rfl⟩
      have he : v = (2 : ℂ) • reflectedBasis hdpos a - reflectedBasis hdpos b := by
        ext i
        change z i = 2 * reflectedBasis hdpos a i - reflectedBasis hdpos b i
        rw [reflectedBasis_entry hdpos, reflectedBasis_entry hdpos, H_entry, H_entry]
        change z i = 2 * ((if i = a then 1 else 0) -
            (2 / (q d : ℂ)) * wc i * wc a) -
          ((if i = b then 1 else 0) - (2 / (q d : ℂ)) * wc i * wc b)
        have hwa : wc a = 1 := by simp [wc, weight, a]
        have hwb : wc b = 2 := by simp [wc, weight, b]
        rw [hwa, hwb]
        simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        ring
      rw [he]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ ha) hb
    intro hc
    have hcard : T.card + T.card ≤ d := by
      simp [T, hab]
      exact hd
    have heq := hc T T hcard
    have hv : v ∈ Submodule.span ℂ ((EuclideanSpace.basisFun (Fin d) ℂ) ''
        (↑T : Set (Fin d))) ⊓ Submodule.span ℂ ((reflectedBasis hdpos) ''
        (↑T : Set (Fin d))) := ⟨hvA, hvB⟩
    rw [heq] at hv
    exact hv_ne ((Submodule.mem_bot ℂ).mp hv)
  intro d hd
  have hp : 0 < d := by omega
  exact ⟨EuclideanSpace.basisFun (Fin d) ℂ, reflectedBasis hp,
    all_noncommuting hp, not_coinc hd⟩
end
end D5.S3.Quantum.Measurements.NoncommutingNotCompletelyIncompatible
