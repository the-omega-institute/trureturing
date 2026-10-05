/- GID: D5/S3/Combinatorics/MatchingEnumeration/BlumTriangle
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MatchingEnumeration/BlumTriangle
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.ToLinearEquiv]
   utility: none
   digest: Blum's exact two-adic matching valuation holds at every positive multiple of four. -/

import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleReduction
import D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleRectangles
import D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleGram
import D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleParity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MatchingEnumeration.BlumTriangle

open BlumTriangleDefs BlumTriangleReduced Finset Matrix

set_option maxHeartbeats 2000000 in
-- The finite block equations and their bilinear expansions share this elaboration budget.
/-- Blum's clause of Propp's Problem 30: the exact power of two dividing the matching count
at triangle order `4k` is `2^k`, for every positive `k`. -/
theorem result : BlumTriangleDefs.claim := by
  classical
  intro k hk
  have hgram := BlumTriangleRectangles.rectangle_gram (K := ZMod 2) k
  have hdet : Matrix.det (fun u v : Vertex (4 * k) =>
      if reducedAdj k u v then (1 : ZMod 2) else 0) = 1 := by
    let V := Vertex (4 * k)
    let E := {u : V // u.1.1.val % 2 = 0}
    let O := {u : V // u.1.1.val % 2 = 1}
    let H : Matrix V V (ZMod 2) := fun u v => if reducedAdj k u v then 1 else 0
    let B : Matrix E E (ZMod 2) := fun u v => H u.1 v.1
    let C : Matrix E O (ZMod 2) := fun u v => H u.1 v.1
    let W : Fin (2 * k) → E → ZMod 2 := fun j u =>
      if u.1.1.1.val / 2 ≤ j.val ∧ j.val ≤ u.1.1.2.val / 2 ∧
        u.1.1.2.val / 2 ≤
          (if j.val % 2 = 0 then 2 * k - 1 else 4 * k - 1 - j.val) then 1 else 0
    change ∀ i j, W i ⬝ᵥ B *ᵥ W j =
      if i = j then 0 else if min i.val j.val % 2 = 0 then 1 else 0 at hgram
    change H.det = 1
    have hsymm (u v : V) : H u v = H v u := by
      have he : reducedAdj k u v ↔ reducedAdj k v u := by
        constructor <;> rintro ⟨he, h1, h2⟩
        · exact ⟨he.elim Or.inr Or.inl, h2, h1⟩
        · exact ⟨he.elim Or.inr Or.inl, h2, h1⟩
      simp only [H, he]
    have odd_zero (u v : O) : H u.1 v.1 = 0 := by
      apply if_neg
      intro he
      have hp := u.2
      have hq := v.2
      rcases he.1 with he | he
      all_goals rcases he with ⟨hr, _⟩ | ⟨hp', _⟩
      all_goals omega
    let oddEquiv : {u : V // ¬ u.1.1.val % 2 = 0} ≃ O :=
      Equiv.subtypeEquivProp (by funext u; exact propext (by omega))
    let split : E ⊕ O ≃ V :=
      (Equiv.sumCongr (Equiv.refl E) oddEquiv.symm).trans
        (Equiv.sumCompl (fun u : V => u.1.1.val % 2 = 0))
    have sum_split (F : V → ZMod 2) :
        (∑ v : V, F v) = (∑ u : E, F u.1) + ∑ u : O, F u.1 := by
      calc
        _ = ∑ u : E ⊕ O, F (split u) :=
          (Fintype.sum_equiv split _ _ (fun _ => rfl)).symm
        _ = _ := by rw [Fintype.sum_sum_type]; rfl
    obtain ⟨e, he, hinj⟩ := reduced_kernel_basis (K := ZMod 2) k
    have synthesis (t : Fin (2 * k) → ZMod 2) :
        (e t).1 = ∑ j : Fin (2 * k), t j • W j := by
      funext u
      rw [he]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply sum_congr rfl
      intro j _
      dsimp [W]
      split_ifs <;> simp
    have wker (j : Fin (2 * k)) : Cᵀ *ᵥ W j = 0 := by
      have hw : (e (Pi.single j 1)).1 = W j := by
        rw [synthesis]
        simp
      rw [← hw]
      exact (e (Pi.single j 1)).2
    have hkernel (z : V → ZMod 2) (hz : H *ᵥ z = 0) : z = 0 := by
      let f : E → ZMod 2 := fun u => z u.1
      let g : O → ZMod 2 := fun u => z u.1
      have fker : Cᵀ *ᵥ f = 0 := by
        funext u
        have h := congrFun hz u.1
        change (∑ v : V, H u.1 v * z v) = 0 at h
        rw [sum_split] at h
        have ho : (∑ v : O, H u.1 v.1 * z v.1) = 0 := by
          apply sum_eq_zero
          intro v _
          rw [odd_zero, zero_mul]
        rw [ho, add_zero] at h
        change (∑ v : E, H v.1 u.1 * z v.1) = 0
        simpa only [hsymm] using h
      have proj : B *ᵥ f + C *ᵥ g = 0 := by
        funext u
        have h := congrFun hz u.1
        change (∑ v : V, H u.1 v * z v) = 0 at h
        rw [sum_split] at h
        exact h
      let t := e.symm ⟨f, fker⟩
      have et : (e t).1 = f := congrArg Subtype.val (e.apply_symm_apply ⟨f, fker⟩)
      have fexp : f = ∑ j : Fin (2 * k), t j • W j := et.symm.trans (synthesis t)
      have pair_zero (i : Fin (2 * k)) : W i ⬝ᵥ B *ᵥ f = 0 := by
        have h := congrArg (fun x => W i ⬝ᵥ x) proj
        have orthogonal : W i ⬝ᵥ C *ᵥ g = 0 := by
          rw [← dotProduct_transpose_mulVec C g (W i), wker, dotProduct_zero]
        rwa [dotProduct_add, orthogonal, add_zero, dotProduct_zero] at h
      have tzero : t = 0 := by
        apply BlumTriangleGram.gram_kernel_zero k t
        funext i
        change (∑ j : Fin (2 * k),
          (if i = j then (0 : ZMod 2) else if min i.val j.val % 2 = 0 then 1 else 0)
            * t j) = 0
        simp_rw [← hgram]
        have expand : W i ⬝ᵥ B *ᵥ f =
            ∑ j : Fin (2 * k), (W i ⬝ᵥ B *ᵥ W j) * t j := by
          rw [fexp]
          change W i ⬝ᵥ B.mulVecLin (∑ j, t j • W j) = _
          rw [map_sum, dotProduct_sum]
          apply sum_congr rfl
          intro j _
          rw [map_smul]
          change W i ⬝ᵥ t j • (B *ᵥ W j) = _
          rw [dotProduct_smul, smul_eq_mul, mul_comm]
        rw [← expand]
        exact pair_zero i
      have fzero : f = 0 := by rw [fexp, tzero]; simp
      have gzero : g = 0 := by
        apply hinj
        change C *ᵥ g = C *ᵥ 0
        simpa only [fzero, mulVec_zero, zero_add] using proj
      funext u
      by_cases hu : u.1.1.val % 2 = 0
      · exact congrFun fzero ⟨u, hu⟩
      · exact congrFun gzero ⟨u, by omega⟩
    have hn : H.det ≠ 0 := by
      intro hz
      obtain ⟨z, hne, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
      exact hne (hkernel z hzero)
    have hb : H.det = 0 ∨ H.det = 1 := by
      have hh := ZMod.val_lt H.det
      have hv : H.det.val = 0 ∨ H.det.val = 1 := by omega
      rcases hv with hv | hv
      · left
        exact ZMod.val_injective 2 (by simpa using hv)
      · right
        exact ZMod.val_injective 2 (by rw [ZMod.val_one_eq_one_mod]; exact hv)
    exact hb.resolve_left hn
  let V := Vertex (4 * k)
  let R := {p : V → V // ∀ u, p (p u) = u ∧ p u ≠ u ∧ reducedAdj k u (p u)}
  let H : Matrix V V (ZMod 2) := fun u v => if reducedAdj k u v then 1 else 0
  change H.det = 1 at hdet
  have hsymm : Hᵀ = H := by
    funext u v
    have he : reducedAdj k v u ↔ reducedAdj k u v := by
      constructor <;> rintro ⟨he, h1, h2⟩
      · exact ⟨he.elim Or.inr Or.inl, h2, h1⟩
      · exact ⟨he.elim Or.inr Or.inl, h2, h1⟩
    change (if reducedAdj k v u then (1 : ZMod 2) else 0) =
      if reducedAdj k u v then 1 else 0
    simp only [he]
  have hdiag (u : V) : H u u = 0 := by
    apply if_neg
    intro he
    rcases he.1 with he | he
    all_goals rcases he with ⟨hr, _⟩ | ⟨_, ⟨_, hx⟩ | ⟨hr, _⟩⟩
    all_goals omega
  have hbits (u v : V) : H u v = 0 ∨ H u v = 1 := by
    dsimp [H]
    split_ifs <;> simp
  have parity := BlumTriangleParity.determinant_matching_parity H hsymm hdiag hbits
  let e : R ≃ {p : V → V // ∀ u, p (p u) = u ∧ p u ≠ u ∧ H u (p u) = 1} :=
    Equiv.subtypeEquivProp (by
      funext p
      apply propext
      have edge_iff (u : V) : H u (p u) = 1 ↔ reducedAdj k u (p u) := by
        by_cases hadj : reducedAdj k u (p u) <;> simp [H, hadj]
      simp only [edge_iff])
  rw [← Nat.card_congr e, hdet] at parity
  have odd_count : ¬ 2 ∣ Nat.card R := by
    intro hd
    have hz := (ZMod.natCast_eq_zero_iff (Nat.card R) 2).mpr hd
    rw [← parity] at hz
    exact one_ne_zero hz
  have count := BlumTriangleReduction.reflection_reduction k hk
  change M (4 * k) = 2 ^ k * Nat.card R at count
  constructor
  · exact ⟨Nat.card R, count⟩
  · intro hd
    rw [count, pow_succ] at hd
    exact odd_count ((mul_dvd_mul_iff_left (pow_ne_zero k (by omega))).mp hd)

end D5.S3.Combinatorics.MatchingEnumeration.BlumTriangle
