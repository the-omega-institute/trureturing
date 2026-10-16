/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer
   mirror-E: none(waiver:algebraic-spectrum-transfer)
   anchors: []
   utility: none
   digest: Ordered rank-three boundary spectra transfer purity bounds by actual middle insertion and deletion. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Fin.InsertNth

set_option autoImplicit false
set_option Elab.async false

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer
open Matrix
open QutritSpectralReduction (K1 K2)

noncomputable section

/-- The three largest and six smallest positions in a tuple of length `n + 9`. -/
def boundaryIndex (n : ℕ) (q : Fin 9) : Fin (n + 9) :=
  if h : q.val < 3 then ⟨q.val, by omega⟩ else ⟨n + q.val, by omega⟩

def boundaryValues (n : ℕ) (l : Fin (n + 9) → ℝ) : Fin 9 → ℝ :=
  fun q => l (boundaryIndex n q)

def purityBound (N : ℕ) : ℝ := ((N : ℝ) + 8) / ((N : ℝ) + 2) ^ 2

/-- This is a rank-three spectral relaxation, with no assertion of APPT sufficiency. -/
def SpectralBound (n : ℕ) : Prop :=
  ∀ l : Fin (n + 9) → ℝ, Antitone l → (∀ i, 0 ≤ l i) →
    (∑ i, l i) = 1 → (K1 (boundaryValues n l)).PosSemidef →
    (K2 (boundaryValues n l)).PosSemidef → ∑ i, (l i) ^ 2 ≤ purityBound (n + 9)

private def middle (n : ℕ) : Fin (n + 9) := ⟨n + 2, by omega⟩

private def insertOne (n : ℕ) (l : Fin (n + 9) → ℝ) : Fin (n + 10) → ℝ :=
  Fin.insertNth ⟨n + 2, by omega⟩ (l (middle n)) l

private def deleteOne (n : ℕ) (l : Fin (n + 10) → ℝ) : Fin (n + 9) → ℝ :=
  Fin.removeNth (middle (n + 1)) l

private theorem insertOne_order (n : ℕ) (l : Fin (n + 9) → ℝ)
    (ho : Antitone l) : Antitone (insertOne n l) := by
  simpa [insertOne, middle] using
    (Fin.insertNth_monotone (α := ℝᵒᵈ) ho (⟨n + 1, by omega⟩ : Fin (n + 8))
      (l (middle n)) (ho (by change n + 1 ≤ n + 2; omega)) le_rfl)

private theorem insertOne_nonneg (n : ℕ) (l : Fin (n + 9) → ℝ)
    (hn : ∀ i, 0 ≤ l i) : ∀ i, 0 ≤ insertOne n l i := by
  intro i
  induction i using Fin.succAboveCases ⟨n + 2, by omega⟩
  · simpa [insertOne] using hn (middle n)
  · simpa [insertOne] using hn _

private theorem insertOne_middle (n : ℕ) (l : Fin (n + 9) → ℝ) :
    insertOne n l (middle (n + 1)) = l (middle n) := by
  have hi : middle (n + 1) =
      (⟨n + 2, by omega⟩ : Fin (n + 10)).succAbove (middle n) := by
    apply Fin.ext
    simp [middle, Fin.succAbove]
  rw [hi]
  exact Fin.insertNth_apply_succAbove _ _ _ _

private theorem insertOne_boundary (n : ℕ) (hn : 1 ≤ n)
    (l : Fin (n + 9) → ℝ) :
    boundaryValues (n + 1) (insertOne n l) = boundaryValues n l := by
  funext q
  have hi : boundaryIndex (n + 1) q =
      (⟨n + 2, by omega⟩ : Fin (n + 10)).succAbove (boundaryIndex n q) := by
    apply Fin.ext
    dsimp [boundaryIndex, Fin.succAbove]
    split_ifs <;> simp_all <;> omega
  change insertOne n l (boundaryIndex (n + 1) q) = l (boundaryIndex n q)
  rw [hi]
  exact Fin.insertNth_apply_succAbove _ _ _ _

private theorem sum_insertOne (n : ℕ) (l : Fin (n + 9) → ℝ) (F : ℝ → ℝ) :
    ∑ i, F (insertOne n l i) = F (l (middle n)) + ∑ i, F (l i) := by
  rw [Fin.sum_univ_succAbove _ (⟨n + 2, by omega⟩ : Fin (n + 10))]
  simp [insertOne]

private theorem insert_copies (a n : ℕ) (hn : 1 ≤ n)
    (l : Fin (n + 9) → ℝ) (ho : Antitone l) (hp : ∀ i, 0 ≤ l i) :
    ∃ v : Fin (n + 9 + a) → ℝ, Antitone v ∧ (∀ i, 0 ≤ v i) ∧
      boundaryValues (n + a) (fun i => v (Fin.cast (by omega) i)) = boundaryValues n l ∧
      (∑ i, v i) = (∑ i, l i) + (a : ℝ) * l (middle n) ∧
      (∑ i, (v i) ^ 2) = (∑ i, (l i) ^ 2) + (a : ℝ) * (l (middle n)) ^ 2 := by
  induction a generalizing n with
  | zero =>
      refine ⟨l, ho, hp, ?_, ?_, ?_⟩ <;> simp
  | succ a ih =>
      obtain ⟨v, hvo, hvp, hvb, hvs, hvq⟩ := ih (n + 1) (by omega)
        (insertOne n l) (insertOne_order n l ho) (insertOne_nonneg n l hp)
      have hdim : n + 1 + 9 + a = n + 9 + (a + 1) := by omega
      let w : Fin (n + 9 + (a + 1)) → ℝ := fun i => v (Fin.cast hdim.symm i)
      have hwF (F : ℝ → ℝ) : (∑ i, F (w i)) = ∑ i, F (v i) := by
        exact Fin.sum_congr' (fun i => F (v i)) hdim.symm
      refine ⟨w, ?_, ?_, ?_, ?_, ?_⟩
      · intro i j hij
        exact hvo (by exact hij)
      · intro i; exact hvp _
      · have hb := insertOne_boundary n hn l
        simpa [w, boundaryValues, boundaryIndex, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using hvb.trans hb
      · rw [hwF, hvs, sum_insertOne, insertOne_middle]
        push_cast
        ring
      · rw [hwF, hvq, sum_insertOne, insertOne_middle]
        push_cast
        ring

private theorem deleteOne_boundary (n : ℕ) (l : Fin (n + 10) → ℝ) :
    boundaryValues n (deleteOne n l) = boundaryValues (n + 1) l := by
  funext q
  change l ((middle (n + 1)).succAbove (boundaryIndex n q)) =
    l (boundaryIndex (n + 1) q)
  congr 1
  apply Fin.ext
  dsimp [middle, boundaryIndex, Fin.succAbove]
  split_ifs <;> simp_all <;> omega

private theorem sum_deleteOne (n : ℕ) (l : Fin (n + 10) → ℝ) (F : ℝ → ℝ) :
    F (l (middle (n + 1))) + ∑ i, F (deleteOne n l i) = ∑ i, F (l i) := by
  exact Fin.add_sum_removeNth (middle (n + 1)) (fun i => F (l i))

private theorem boundary_div (n : ℕ) (l : Fin (n + 9) → ℝ) (s : ℝ) :
    boundaryValues n (fun i => l i / s) = fun q => boundaryValues n l q / s := rfl

private theorem K1_div (b : Fin 9 → ℝ) (s : ℝ) :
    K1 (fun q => b q / s) = (1 / s) • K1 b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [K1, Matrix.smul_apply] <;> ring

private theorem K2_div (b : Fin 9 → ℝ) (s : ℝ) :
    K2 (fun q => b q / s) = (1 / s) • K2 b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [K2, Matrix.smul_apply] <;> ring

private theorem unnormalized_bound (n : ℕ) (hb : SpectralBound n)
    (l : Fin (n + 9) → ℝ) (ho : Antitone l) (hn : ∀ i, 0 ≤ l i)
    (hs : 0 < ∑ i, l i) (h1 : (K1 (boundaryValues n l)).PosSemidef)
    (h2 : (K2 (boundaryValues n l)).PosSemidef) :
    ∑ i, (l i) ^ 2 ≤ purityBound (n + 9) * (∑ i, l i) ^ 2 := by
  let s := ∑ i, l i
  have hs' : 0 < s := hs
  have hp := hb (fun i => l i / s)
    (fun i j hij => div_le_div_of_nonneg_right (ho hij) hs'.le)
    (fun i => div_nonneg (hn i) hs'.le)
    (by rw [← Finset.sum_div]; exact div_self hs'.ne')
    (by rw [boundary_div, K1_div]; exact h1.smul (by positivity))
    (by rw [boundary_div, K2_div]; exact h2.smul (by positivity))
  simp_rw [div_pow] at hp
  rw [← Finset.sum_div] at hp
  exact (div_le_iff₀ (sq_pos_of_pos hs')).mp hp

private theorem middle_cap (n : ℕ) (l : Fin (n + 10) → ℝ)
    (ho : Antitone l) (ht : ∑ i, l i = 1)
    (h1 : (K1 (boundaryValues (n + 1) l)).PosSemidef) :
    ((n : ℝ) + 7) * l (middle (n + 1)) ≤ 1 := by
  let t := l (middle (n + 1))
  let B := ∑ j : Fin 6, l ⟨n + 4 + j.val, by omega⟩
  let T := l 0 + l 1 + l 2
  have hquad := h1.dotProduct_mulVec_nonneg (![1, 1, 1] : Fin 3 → ℝ)
  have hTB : T ≤ B := by
    dsimp [T, B]
    norm_num [K1, boundaryValues, boundaryIndex, dotProduct, Matrix.mulVec,
      Fin.sum_univ_succ] at hquad ⊢
    linarith
  have hT : 3 * t ≤ T := by
    have h0 := ho (show (0 : Fin (n + 10)) ≤ middle (n + 1) by
      change 0 ≤ n + 1 + 2; omega)
    have h1' := ho (show (1 : Fin (n + 10)) ≤ middle (n + 1) by
      change 1 ≤ n + 1 + 2; omega)
    have h2' := ho (show (2 : Fin (n + 10)) ≤ middle (n + 1) by
      change 2 ≤ n + 1 + 2; omega)
    dsimp [T, t]
    linarith
  have hprefix : ((n + 4 : ℕ) : ℝ) * t ≤
      ∑ j : Fin (n + 4), l ⟨j.val, by omega⟩ := by
    calc
      _ = ∑ _j : Fin (n + 4), t := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => ho (by
        change j.val ≤ n + 1 + 2
        omega)
  have hsplit : (∑ j : Fin (n + 4), l ⟨j.val, by omega⟩) + B = 1 := by
    rw [Fin.sum_univ_add (a := n + 4) (b := 6) l] at ht
    simpa [B, Fin.castAdd, Fin.natAdd] using ht
  push_cast at hprefix
  dsimp [t] at hT hprefix
  linarith

private def scalarF (x : ℝ) : ℝ := (x + 8) / (x + 2) ^ 2

private theorem insertion_scalar (N a t : ℝ) (hN : 10 ≤ N) (ha : 1 ≤ a)
    (ht : 0 ≤ t) (hsmall : t ≤ 1 / (N + 2)) :
    scalarF (N + a) * (1 + a * t) ^ 2 - a * t ^ 2 ≤ scalarF N := by
  have hN0 : 0 ≤ N := by linarith
  have hD : 0 < N + 2 := by linarith
  have hE : 0 < N + a + 2 := by linarith
  have hcoef : a * scalarF (N + a) - 1 < 0 := by
    have ha0 : 0 < a := by linarith
    have hN4 : 0 < N - 4 := by linarith
    have hpoly : 0 < (N + 2) ^ 2 + a * (N - 4) := by positivity
    have hid : a * scalarF (N + a) - 1 =
        -((N + 2) ^ 2 + a * (N - 4)) / (N + a + 2) ^ 2 := by
      unfold scalarF
      field_simp [hE.ne']
      <;> ring
    rw [hid]
    exact div_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos hE)
  have hend : 2 * scalarF (N + a) +
      (a * scalarF (N + a) - 1) * (2 / (N + 2)) =
        12 / ((N + a + 2) * (N + 2)) := by
    unfold scalarF
    field_simp [hD.ne', hE.ne']
    <;> ring
  have hfactor : 0 ≤ 2 * scalarF (N + a) +
      (a * scalarF (N + a) - 1) * (1 / (N + 2) + t) := by
    have hprod := mul_le_mul_of_nonpos_left
      (show 1 / (N + 2) + t ≤ 2 / (N + 2) by linarith) hcoef.le
    have hpos : 0 < 12 / ((N + a + 2) * (N + 2)) := by positivity
    linarith
  have hid : scalarF N - (scalarF (N + a) * (1 + a * t) ^ 2 - a * t ^ 2) =
      a * (1 / (N + 2) - t) *
        (2 * scalarF (N + a) + (a * scalarF (N + a) - 1) * (1 / (N + 2) + t)) := by
    unfold scalarF
    field_simp [hD.ne', hE.ne']
    <;> ring
  have hp := mul_nonneg (mul_nonneg (by linarith : 0 ≤ a)
    (sub_nonneg.mpr hsmall)) hfactor
  linarith

private theorem deletion_scalar (N t : ℝ) (hN : 10 ≤ N)
    (hlarge : 1 / (N + 2) ≤ t) (hcap : (N - 3) * t ≤ 1) :
    scalarF (N - 1) * (1 - t) ^ 2 + t ^ 2 ≤ scalarF N := by
  let r := (N ^ 2 + 15 * N + 20) / ((N ^ 2 + 3 * N + 8) * (N + 2))
  have hN0 : 0 ≤ N := by linarith
  have hD : 0 < N + 2 := by linarith
  have hE : 0 < N + 1 := by linarith
  have hC : 0 < N - 3 := by linarith
  have hQ : 0 < N ^ 2 + 3 * N + 8 := by positivity
  have hpoly : 0 ≤ 7 * N ^ 2 - 39 * N - 76 := by
    nlinarith [sq_nonneg (N - 10)]
  have hroot : 1 / (N - 3) ≤ r := by
    dsimp [r]
    apply (div_le_div_iff₀ hC (mul_pos hQ hD)).mpr
    nlinarith
  have htr : t ≤ r := le_trans ((le_div_iff₀ hC).mpr (by nlinarith)) hroot
  have hid : scalarF (N - 1) * (1 - t) ^ 2 + t ^ 2 - scalarF N =
      (scalarF (N - 1) + 1) * (t - 1 / (N + 2)) * (t - r) := by
    dsimp [r, scalarF]
    rw [show N - 1 + 2 = N + 1 by ring]
    field_simp [hD.ne', hE.ne', hQ.ne']
    <;> ring
  have hcoef : 0 ≤ scalarF (N - 1) + 1 := by
    have hnum : 0 ≤ N - 1 + 8 := by linarith
    exact add_nonneg (div_nonneg hnum (sq_nonneg _)) zero_le_one
  have hp := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg hcoef (sub_nonneg.mpr hlarge)) (sub_nonpos.mpr htr)
  linarith

/-
proof_shape: spectral_bound_transfer: content
escape_witness: the actual last middle coordinate controls two different
  normalized endpoint spectra; order, extremal coordinates and both moments
  are established above for the constructed tuples, not supplied as premises.
admission_basis: escape-witness
-/
/-- For `N = n + 10`, bounds at `N - 1` and `N + a` imply the bound at `N`.
Ties and zero coordinates are allowed. Only an actual coordinate is deleted. -/
theorem spectral_bound_transfer (n a : ℕ) (ha : 1 ≤ a)
    (hprev : SpectralBound n) (hnext : SpectralBound (n + 1 + a)) :
    SpectralBound (n + 1) := by
  intro l ho hn ht h1 h2
  let t := l (middle (n + 1))
  have ht0 : 0 ≤ t := hn _
  have hcap := middle_cap n l ho ht h1
  have hN : (10 : ℝ) ≤ (n : ℝ) + 10 := by nlinarith [Nat.cast_nonneg n]
  have hcurrent : purityBound (n + 1 + 9) = scalarF ((n : ℝ) + 10) := by
    unfold purityBound scalarF
    push_cast
    congr 1 <;> ring
  change ∑ i, (l i) ^ 2 ≤ purityBound (n + 1 + 9)
  by_cases hsmall : t ≤ 1 / ((n : ℝ) + 12)
  · obtain ⟨v, hvo, hvn, hvb, hvs, hvq⟩ := insert_copies a (n + 1) (by omega) l ho hn
    let w : Fin (n + 1 + a + 9) → ℝ := fun i => v (Fin.cast (by omega) i)
    have hwF (F : ℝ → ℝ) : (∑ i, F (w i)) = ∑ i, F (v i) := by
      exact Fin.sum_congr' (fun i => F (v i)) (by omega)
    have hws : ∑ i, w i = 1 + (a : ℝ) * t := by rw [hwF, hvs, ht]
    have hwq : ∑ i, (w i) ^ 2 = (∑ i, (l i) ^ 2) + (a : ℝ) * t ^ 2 := by
      rw [hwF, hvq]
    have hwb : boundaryValues (n + 1 + a) w = boundaryValues (n + 1) l := hvb
    have hp := unnormalized_bound (n + 1 + a) hnext w
      (fun i j hij => hvo (by exact hij)) (fun i => hvn _)
      (by rw [hws]; positivity) (by rw [hwb]; exact h1) (by rw [hwb]; exact h2)
    rw [hwq, hws] at hp
    have hs := insertion_scalar ((n : ℝ) + 10) a t hN (by exact_mod_cast ha) ht0
      (by simpa only [add_assoc] using hsmall)
    have hendpoint : purityBound (n + 1 + a + 9) = scalarF ((n : ℝ) + 10 + a) := by
      unfold purityBound scalarF
      push_cast
      congr 1 <;> ring
    rw [hendpoint] at hp
    rw [hcurrent]
    calc
      _ ≤ scalarF ((n : ℝ) + 10 + a) * (1 + (a : ℝ) * t) ^ 2 - (a : ℝ) * t ^ 2 := by
        linarith
      _ ≤ _ := hs
  · have hlarge : 1 / ((n : ℝ) + 12) ≤ t := le_of_lt (lt_of_not_ge hsmall)
    have ht1 : t < 1 := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      change ((n : ℝ) + 7) * t ≤ 1 at hcap
      nlinarith [mul_nonneg hn0 ht0]
    let v := deleteOne n l
    have hvb : boundaryValues n v = boundaryValues (n + 1) l := deleteOne_boundary n l
    have hvs : ∑ i, v i = 1 - t := by
      have h := sum_deleteOne n l id
      dsimp [id] at h
      rw [ht] at h
      linarith
    have hvq : ∑ i, (v i) ^ 2 = (∑ i, (l i) ^ 2) - t ^ 2 := by
      have h := sum_deleteOne n l (fun x => x ^ 2)
      linarith
    have hp := unnormalized_bound n hprev v
      (ho.comp (Fin.strictMono_succAbove (middle (n + 1))).monotone)
      (fun i => hn _) (by rw [hvs]; linarith)
      (by rw [hvb]; exact h1) (by rw [hvb]; exact h2)
    rw [hvs, hvq] at hp
    have hs := deletion_scalar ((n : ℝ) + 10) t hN
      (by simpa only [add_assoc] using hlarge) (by convert hcap using 1 <;> dsimp [t] <;> ring)
    have hendpoint : purityBound (n + 9) = scalarF (((n : ℝ) + 10) - 1) := by
      unfold purityBound scalarF
      push_cast
      congr 1 <;> ring
    rw [hendpoint] at hp
    rw [hcurrent]
    calc
      _ ≤ scalarF (((n : ℝ) + 10) - 1) * (1 - t) ^ 2 + t ^ 2 := by linarith
      _ ≤ _ := hs

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer
