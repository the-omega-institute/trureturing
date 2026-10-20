/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer
   mirror-E: none(waiver:algebraic-spectrum-transfer)
   anchors: []
   utility: none
   digest: Ordered rank-three and rank-four spectra transfer bounds by actual middle surgery. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction
import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN8PurityBound
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
  have hmon : @Monotone (Fin (n + 10)) ℝᵒᵈ _ _
      (Fin.insertNth (⟨n + 2, by omega⟩ : Fin (n + 10)) (l (middle n)) l) := by
    convert (Fin.insertNth_monotone (α := ℝᵒᵈ)
      (f := fun i => (l i : ℝᵒᵈ)) ho (⟨n + 1, by omega⟩ : Fin (n + 8))
      (l (middle n)) (ho (by change n + 1 ≤ n + 2; omega)) le_rfl) using 1
    congr 1
  exact hmon

private theorem insertOne_nonneg (n : ℕ) (l : Fin (n + 9) → ℝ)
    (hn : ∀ i, 0 ≤ l i) : ∀ i, 0 ≤ insertOne n l i := by
  intro i
  induction i using Fin.succAboveCases (⟨n + 2, by omega⟩ : Fin (n + 10))
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
        funext q
        have h := congrFun (hvb.trans hb) q
        change v _ = _ at h
        change v _ = _
        convert h using 1
        congr 1
        apply Fin.ext
        simp only [boundaryIndex, Fin.val_cast]
        split_ifs <;> simp_all <;> omega
      · have hw := hwF id
        simp only [id_eq] at hw
        have hi := sum_insertOne n l id
        simp only [id_eq] at hi
        rw [hw, hvs, hi, insertOne_middle]
        push_cast
        ring
      · rw [hwF (fun x => x ^ 2), hvq, sum_insertOne n l (fun x => x ^ 2), insertOne_middle]
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
  let T := l ⟨0, by omega⟩ + l ⟨1, by omega⟩ + l ⟨2, by omega⟩
  have hquad := h1.dotProduct_mulVec_nonneg (![1, 1, 1] : Fin 3 → ℝ)
  have hTB : T ≤ B := by
    dsimp [T, B]
    norm_num [K1, boundaryValues, boundaryIndex, dotProduct, Matrix.mulVec,
      Fin.sum_univ_succ, Nat.add_assoc] at hquad ⊢
    linarith
  have hT : 3 * t ≤ T := by
    have h0 := ho (show (⟨0, by omega⟩ : Fin (n + 10)) ≤ middle (n + 1) by
      change 0 ≤ n + 1 + 2; omega)
    have h1' := ho (show (⟨1, by omega⟩ : Fin (n + 10)) ≤ middle (n + 1) by
      change 1 ≤ n + 1 + 2; omega)
    have h2' := ho (show (⟨2, by omega⟩ : Fin (n + 10)) ≤ middle (n + 1) by
      change 2 ≤ n + 1 + 2; omega)
    calc
      3 * t = t + t + t := by ring
      _ ≤ T := add_le_add (add_le_add h0 h1') h2'
  have hprefix : ((n + 4 : ℕ) : ℝ) * t ≤
      ∑ j : Fin (n + 4), l ⟨j.val, by omega⟩ := by
    calc
      _ = ∑ _j : Fin (n + 4), t := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => ho (by
        change j.val ≤ n + 1 + 2
        omega)
  have hsplit : (∑ j : Fin (n + 4), l ⟨j.val, by omega⟩) + B = 1 := by
    rw [Fin.sum_univ_add (a := n + 4) (b := 6) l] at ht
    simpa [B, Fin.castAdd, Fin.natAdd, Fin.castLE] using ht
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
      (show 1 / (N + 2) + t ≤ 2 / (N + 2) by
        calc
          1 / (N + 2) + t ≤ 1 / (N + 2) + 1 / (N + 2) :=
            add_le_add (le_rfl : 1 / (N + 2) ≤ 1 / (N + 2)) hsmall
          _ = 2 / (N + 2) := by ring) hcoef.le
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

private theorem deletion_scalar (N kappa t : ℝ) (hN : 10 ≤ N)
    (hC : 0 < N - kappa)
    (hguard : 0 ≤ (10 - kappa) * N ^ 2 + (6 - 15 * kappa) * N - 20 * kappa - 16)
    (hlarge : 1 / (N + 2) ≤ t) (hcap : (N - kappa) * t ≤ 1) :
    scalarF (N - 1) * (1 - t) ^ 2 + t ^ 2 ≤ scalarF N := by
  let r := (N ^ 2 + 15 * N + 20) / ((N ^ 2 + 3 * N + 8) * (N + 2))
  have hN0 : 0 ≤ N := by linarith
  have hD : 0 < N + 2 := by linarith
  have hE : 0 < N + 1 := by linarith
  have hQ : 0 < N ^ 2 + 3 * N + 8 := by positivity
  have hroot : 1 / (N - kappa) ≤ r := by
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
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hN : (10 : ℝ) ≤ (n : ℝ) + 10 := by linarith
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
    have hws : ∑ i, w i = 1 + (a : ℝ) * t := by
      have hw := hwF id
      simp only [id_eq] at hw
      rw [hw, hvs, ht]
    have hwq : ∑ i, (w i) ^ 2 = (∑ i, (l i) ^ 2) + (a : ℝ) * t ^ 2 := by
      rw [hwF (fun x => x ^ 2), hvq]
    have hwb : boundaryValues (n + 1 + a) w = boundaryValues (n + 1) l := hvb
    have hp := unnormalized_bound (n + 1 + a) hnext w
      (fun i j hij => hvo (by exact hij)) (fun i => hvn _)
      (by rw [hws]; positivity) (by rw [hwb]; exact h1) (by rw [hwb]; exact h2)
    rw [hwq, hws] at hp
    have hs := insertion_scalar ((n : ℝ) + 10) a t hN (by exact_mod_cast ha) ht0
      (by simpa only [add_assoc, show (10 : ℝ) + 2 = 12 by norm_num] using hsmall)
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
      (fun i j hij => ho ((Fin.strictMono_succAbove (middle (n + 1))).monotone hij))
      (fun i => hn _) (by rw [hvs]; linarith)
      (by rw [hvb]; exact h1) (by rw [hvb]; exact h2)
    rw [hvs, hvq] at hp
    have hs := deletion_scalar ((n : ℝ) + 10) 3 t hN (by linarith)
      (by nlinarith [sq_nonneg (n : ℝ)])
      (by simpa only [add_assoc, show (10 : ℝ) + 2 = 12 by norm_num] using hlarge)
      (by convert hcap using 1 <;> dsimp [t] <;> ring)
    have hendpoint : purityBound (n + 9) = scalarF (((n : ℝ) + 10) - 1) := by
      unfold purityBound scalarF
      push_cast
      congr 1 <;> ring
    rw [hendpoint] at hp
    rw [hcurrent]
    calc
      _ ≤ scalarF (((n : ℝ) + 10) - 1) * (1 - t) ^ 2 + t ^ 2 := by linarith
      _ ≤ _ := hs

#print axioms spectral_bound_transfer


/-- The actual first six and last ten coordinates in dimension `n + 16`. -/
def rankFourBoundaryIndex (n : ℕ) (q : Fin 16) : Fin (n + 16) :=
  if h : q.val < 6 then ⟨q.val, by omega⟩ else ⟨n + q.val, by omega⟩

def rankFourBoundaryValues (n : ℕ) (l : Fin (n + 16) → ℝ) : Fin 16 → ℝ :=
  fun q => l (rankFourBoundaryIndex n q)

/-- Necessary spectral conditions only; this predicate does not assert APPT sufficiency. -/
def RankFourSpectralBound (n : ℕ) : Prop :=
  ∀ l : Fin (n + 16) → ℝ, Antitone l → (∀ i, 0 ≤ l i) →
    (∑ i, l i) = 1 → (K1 (boundaryValues (n + 7) l)).PosSemidef →
    (K2 (boundaryValues (n + 7) l)).PosSemidef →
    UniformRankFourNecessary.sumFirst 6 l ≤ UniformRankFourNecessary.sumLast 10 l →
    ∑ i, (l i) ^ 2 ≤ purityBound (n + 16)

private theorem rankFour_qutrit (n : ℕ) (l : Fin (n + 16) → ℝ) :
    boundaryValues (n + 7) l = fun q : Fin 9 =>
      rankFourBoundaryValues n l ⟨if q.val < 3 then q.val else q.val + 7, by
        split_ifs <;> omega⟩ := by
  funext q
  dsimp [boundaryValues, boundaryIndex, rankFourBoundaryValues, rankFourBoundaryIndex]
  split_ifs <;> congr 1 <;> apply Fin.ext <;> simp_all <;> omega

private theorem rankFour_mass (n : ℕ) (l : Fin (n + 16) → ℝ) :
    (UniformRankFourNecessary.sumFirst 6 l ≤ UniformRankFourNecessary.sumLast 10 l) ↔
    (∑ q : Fin 6, rankFourBoundaryValues n l ⟨q.val, by omega⟩) ≤
      ∑ q : Fin 10, rankFourBoundaryValues n l ⟨6 + q.val, by omega⟩ := by
  have hhead (q : Fin 6) : q.val < n + 16 := by omega
  have htail (q : Fin 10) : n + 16 - 10 + q.val < n + 16 := by omega
  simp only [UniformRankFourNecessary.sumFirst, UniformRankFourNecessary.sumLast,
    dite_eq_left (hhead _), dite_eq_left (htail _)]
  have hfirst : (∑ q : Fin 6, rankFourBoundaryValues n l ⟨q.val, by omega⟩) =
      ∑ q : Fin 6, l ⟨q.val, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro q _
    simp [rankFourBoundaryValues, rankFourBoundaryIndex, q.isLt]
  have hlast : (∑ q : Fin 10, rankFourBoundaryValues n l ⟨6 + q.val, by omega⟩) =
      ∑ q : Fin 10, l ⟨n + 16 - 10 + q.val, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro q _
    dsimp [rankFourBoundaryValues, rankFourBoundaryIndex]
    rw [dite_eq_right (by omega)]
    congr 1
    apply Fin.ext
    simp
    omega
  rw [hfirst, hlast]

private theorem rankFour_preservation (n m : ℕ) (l : Fin (n + 16) → ℝ)
    (v : Fin (m + 16) → ℝ)
    (hb : rankFourBoundaryValues m v = rankFourBoundaryValues n l) :
    boundaryValues (m + 7) v = boundaryValues (n + 7) l ∧
    ((UniformRankFourNecessary.sumFirst 6 v ≤ UniformRankFourNecessary.sumLast 10 v) ↔
      (UniformRankFourNecessary.sumFirst 6 l ≤ UniformRankFourNecessary.sumLast 10 l)) := by
  constructor
  · rw [rankFour_qutrit, rankFour_qutrit, hb]
  · rw [rankFour_mass, rankFour_mass, hb]

private def rankFourMiddle (n : ℕ) : Fin (n + 16) := ⟨n + 5, by omega⟩

private def rankFourInsert (n : ℕ) (l : Fin (n + 16) → ℝ) : Fin (n + 17) → ℝ :=
  Fin.insertNth ⟨n + 5, by omega⟩ (l (rankFourMiddle n)) l

private def rankFourDelete (n : ℕ) (l : Fin (n + 17) → ℝ) : Fin (n + 16) → ℝ :=
  Fin.removeNth (rankFourMiddle (n + 1)) l

private theorem rankFourInsert_order (n : ℕ) (l : Fin (n + 16) → ℝ)
    (ho : Antitone l) : Antitone (rankFourInsert n l) := by
  have hmon : @Monotone (Fin (n + 17)) ℝᵒᵈ _ _
      (Fin.insertNth (⟨n + 5, by omega⟩ : Fin (n + 17)) (l (rankFourMiddle n)) l) := by
    convert (Fin.insertNth_monotone (α := ℝᵒᵈ)
      (f := fun i => (l i : ℝᵒᵈ)) ho (⟨n + 4, by omega⟩ : Fin (n + 15))
      (l (rankFourMiddle n)) (ho (by change n + 4 ≤ n + 5; omega)) le_rfl) using 1
    congr 1
  exact hmon

private theorem rankFourInsert_nonneg (n : ℕ) (l : Fin (n + 16) → ℝ)
    (hn : ∀ i, 0 ≤ l i) : ∀ i, 0 ≤ rankFourInsert n l i := by
  intro i
  induction i using Fin.succAboveCases (⟨n + 5, by omega⟩ : Fin (n + 17))
  · simpa [rankFourInsert] using hn (rankFourMiddle n)
  · simpa [rankFourInsert] using hn _

private theorem rankFourInsert_middle (n : ℕ) (l : Fin (n + 16) → ℝ) :
    rankFourInsert n l (rankFourMiddle (n + 1)) = l (rankFourMiddle n) := by
  have hi : rankFourMiddle (n + 1) =
      (⟨n + 5, by omega⟩ : Fin (n + 17)).succAbove (rankFourMiddle n) := by
    apply Fin.ext
    simp [rankFourMiddle, Fin.succAbove]
  rw [hi]
  exact Fin.insertNth_apply_succAbove _ _ _ _

private theorem rankFourInsert_boundary (n : ℕ) (hn : 1 ≤ n)
    (l : Fin (n + 16) → ℝ) :
    rankFourBoundaryValues (n + 1) (rankFourInsert n l) = rankFourBoundaryValues n l := by
  funext q
  have hi : rankFourBoundaryIndex (n + 1) q =
      (⟨n + 5, by omega⟩ : Fin (n + 17)).succAbove (rankFourBoundaryIndex n q) := by
    apply Fin.ext
    dsimp [rankFourBoundaryIndex, Fin.succAbove]
    split_ifs <;> simp_all <;> omega
  change rankFourInsert n l (rankFourBoundaryIndex (n + 1) q) =
    l (rankFourBoundaryIndex n q)
  rw [hi]
  exact Fin.insertNth_apply_succAbove _ _ _ _

private theorem sum_rankFourInsert (n : ℕ) (l : Fin (n + 16) → ℝ) (F : ℝ → ℝ) :
    ∑ i, F (rankFourInsert n l i) = F (l (rankFourMiddle n)) + ∑ i, F (l i) := by
  rw [Fin.sum_univ_succAbove _ (⟨n + 5, by omega⟩ : Fin (n + 17))]
  simp [rankFourInsert]

private theorem rankFour_insert_copies (a n : ℕ) (hn : 1 ≤ n)
    (l : Fin (n + 16) → ℝ) (ho : Antitone l) (hp : ∀ i, 0 ≤ l i) :
    ∃ v : Fin (n + 16 + a) → ℝ, Antitone v ∧ (∀ i, 0 ≤ v i) ∧
      rankFourBoundaryValues (n + a) (fun i => v (Fin.cast (by omega) i)) =
        rankFourBoundaryValues n l ∧
      (∑ i, v i) = (∑ i, l i) + (a : ℝ) * l (rankFourMiddle n) ∧
      (∑ i, (v i) ^ 2) = (∑ i, (l i) ^ 2) + (a : ℝ) * (l (rankFourMiddle n)) ^ 2 := by
  induction a generalizing n with
  | zero => refine ⟨l, ho, hp, ?_, ?_, ?_⟩ <;> simp
  | succ a ih =>
      obtain ⟨v, hvo, hvp, hvb, hvs, hvq⟩ := ih (n + 1) (by omega)
        (rankFourInsert n l) (rankFourInsert_order n l ho) (rankFourInsert_nonneg n l hp)
      have hdim : n + 1 + 16 + a = n + 16 + (a + 1) := by omega
      let w : Fin (n + 16 + (a + 1)) → ℝ := fun i => v (Fin.cast hdim.symm i)
      have hwF (F : ℝ → ℝ) : (∑ i, F (w i)) = ∑ i, F (v i) := by
        exact Fin.sum_congr' (fun i => F (v i)) hdim.symm
      refine ⟨w, ?_, ?_, ?_, ?_, ?_⟩
      · intro i j hij; exact hvo (by exact hij)
      · intro i; exact hvp _
      · have hb := rankFourInsert_boundary n hn l
        funext q
        have h := congrFun (hvb.trans hb) q
        change v _ = _ at h
        change v _ = _
        convert h using 1
        congr 1
        apply Fin.ext
        simp only [rankFourBoundaryIndex, Fin.val_cast]
        split_ifs <;> simp_all <;> omega
      · have hw := hwF id
        simp only [id_eq] at hw
        have hi := sum_rankFourInsert n l id
        simp only [id_eq] at hi
        rw [hw, hvs, hi, rankFourInsert_middle]
        push_cast
        ring
      · rw [hwF (fun x => x ^ 2), hvq, sum_rankFourInsert n l (fun x => x ^ 2),
          rankFourInsert_middle]
        push_cast
        ring

private theorem rankFourDelete_boundary (n : ℕ) (l : Fin (n + 17) → ℝ) :
    rankFourBoundaryValues n (rankFourDelete n l) = rankFourBoundaryValues (n + 1) l := by
  funext q
  change l ((rankFourMiddle (n + 1)).succAbove (rankFourBoundaryIndex n q)) =
    l (rankFourBoundaryIndex (n + 1) q)
  congr 1
  apply Fin.ext
  dsimp [rankFourMiddle, rankFourBoundaryIndex, Fin.succAbove]
  split_ifs <;> simp_all <;> omega

private theorem sum_rankFourDelete (n : ℕ) (l : Fin (n + 17) → ℝ) (F : ℝ → ℝ) :
    F (l (rankFourMiddle (n + 1))) + ∑ i, F (rankFourDelete n l i) = ∑ i, F (l i) := by
  exact Fin.add_sum_removeNth (rankFourMiddle (n + 1)) (fun i => F (l i))

private theorem rankFour_unnormalized_bound (n : ℕ) (hb : RankFourSpectralBound n)
    (l : Fin (n + 16) → ℝ) (ho : Antitone l) (hn : ∀ i, 0 ≤ l i)
    (hs : 0 < ∑ i, l i) (h1 : (K1 (boundaryValues (n + 7) l)).PosSemidef)
    (h2 : (K2 (boundaryValues (n + 7) l)).PosSemidef)
    (h4 : UniformRankFourNecessary.sumFirst 6 l ≤ UniformRankFourNecessary.sumLast 10 l) :
    ∑ i, (l i) ^ 2 ≤ purityBound (n + 16) * (∑ i, l i) ^ 2 := by
  let s := ∑ i, l i
  have hs' : 0 < s := hs
  have h4' : UniformRankFourNecessary.sumFirst 6 (fun i => l i / s) ≤
      UniformRankFourNecessary.sumLast 10 (fun i => l i / s) := by
    rw [rankFour_mass] at h4 ⊢
    simp only [rankFourBoundaryValues] at h4 ⊢
    rw [← Finset.sum_div, ← Finset.sum_div]
    exact div_le_div_of_nonneg_right h4 hs'.le
  have hp := hb (fun i => l i / s)
    (fun i j hij => div_le_div_of_nonneg_right (ho hij) hs'.le)
    (fun i => div_nonneg (hn i) hs'.le)
    (by rw [← Finset.sum_div]; exact div_self hs'.ne')
    (by rw [boundary_div, K1_div]; exact h1.smul (by positivity))
    (by rw [boundary_div, K2_div]; exact h2.smul (by positivity)) h4'
  simp_rw [div_pow] at hp
  rw [← Finset.sum_div] at hp
  exact (div_le_iff₀ (sq_pos_of_pos hs')).mp hp

private theorem rankFour_middle_cap (n : ℕ) (hn : 8 ≤ n)
    (l : Fin (n + 17) → ℝ) (ho : Antitone l) (ht : ∑ i, l i = 1)
    (h4 : UniformRankFourNecessary.sumFirst 6 l ≤ UniformRankFourNecessary.sumLast 10 l) :
    ((n : ℝ) + 13) * l (rankFourMiddle (n + 1)) ≤ 1 := by
  let t := l (rankFourMiddle (n + 1))
  let B := ∑ j : Fin 10, l ⟨n + 7 + j.val, by omega⟩
  let T := ∑ j : Fin 6, l ⟨j.val, by omega⟩
  have hTB : T ≤ B := by
    rw [rankFour_mass] at h4
    simpa [T, B, rankFourBoundaryValues, rankFourBoundaryIndex,
      show ∀ j : Fin 10, ¬ (6 + j.val < 6) by omega, ← Nat.add_assoc] using h4
  have hT : 6 * t ≤ T := by
    calc
      _ = ∑ _j : Fin 6, t := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => ho (by
        change j.val ≤ n + 1 + 5
        omega)
  have hprefix : ((n + 7 : ℕ) : ℝ) * t ≤
      ∑ j : Fin (n + 7), l ⟨j.val, by omega⟩ := by
    calc
      _ = ∑ _j : Fin (n + 7), t := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => ho (by
        change j.val ≤ n + 1 + 5
        omega)
  have hsplit : (∑ j : Fin (n + 7), l ⟨j.val, by omega⟩) + B = 1 := by
    rw [Fin.sum_univ_add (a := n + 7) (b := 10) l] at ht
    simpa [B, Fin.castAdd, Fin.natAdd, Fin.castLE] using ht
  push_cast at hprefix
  dsimp [t] at hT hprefix
  linarith

/-
proof_shape: rank_four_spectral_bound_transfer: content
admission_basis: escape-witness
escape_witness: Actual middle-coordinate insertion and deletion preserve the
first-six and last-ten observation, both qutrit pencils, and the rank-four
mass inequality. That inequality supplies the stronger derived pivot cap.
The scalar factorizations above are reused at kappa=4.
-/
/-- At dimension `N = n + 17 >= 25`, bounds at `N-1` and `N+a` give the bound at `N`. -/
theorem rank_four_spectral_bound_transfer (n a : ℕ) (hn : 8 ≤ n) (ha : 1 ≤ a)
    (hprev : RankFourSpectralBound n) (hnext : RankFourSpectralBound (n + 1 + a)) :
    ∀ l : Fin (n + 17) → ℝ, Antitone l → (∀ i, 0 ≤ l i) → (∑ i, l i) = 1 →
    (K1 (boundaryValues (n + 8) l)).PosSemidef →
    (K2 (boundaryValues (n + 8) l)).PosSemidef →
    UniformRankFourNecessary.sumFirst 6 l ≤ UniformRankFourNecessary.sumLast 10 l →
    ∑ i, (l i)^2 ≤ purityBound (n + 17) := by
  intro l ho hp ht h1 h2 h4
  let t := l (rankFourMiddle (n + 1))
  have ht0 : 0 ≤ t := hp _
  have hcap := rankFour_middle_cap n hn l ho ht h4
  have hn0 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (10 : ℝ) ≤ (n : ℝ) + 17 := by linarith
  have hcurrent : purityBound (n + 1 + 16) = scalarF ((n : ℝ) + 17) := by
    unfold purityBound scalarF
    push_cast
    congr 1 <;> ring
  change ∑ i, (l i) ^ 2 ≤ purityBound (n + 1 + 16)
  by_cases hsmall : t ≤ 1 / ((n : ℝ) + 19)
  · obtain ⟨v, hvo, hvn, hvb, hvs, hvq⟩ := rankFour_insert_copies a (n + 1) (by omega) l ho hp
    let w : Fin (n + 1 + a + 16) → ℝ := fun i => v (Fin.cast (by omega) i)
    have hwF (F : ℝ → ℝ) : (∑ i, F (w i)) = ∑ i, F (v i) := by
      exact Fin.sum_congr' (fun i => F (v i)) (by omega)
    have hws : ∑ i, w i = 1 + (a : ℝ) * t := by
      have hw := hwF id
      simp only [id_eq] at hw
      rw [hw, hvs, ht]
    have hwq : ∑ i, (w i) ^ 2 = (∑ i, (l i) ^ 2) + (a : ℝ) * t ^ 2 := by
      rw [hwF (fun x => x ^ 2), hvq]
    have hwb : rankFourBoundaryValues (n + 1 + a) w = rankFourBoundaryValues (n + 1) l := hvb
    obtain ⟨hb, hmass⟩ := rankFour_preservation (n + 1) (n + 1 + a) l w hwb
    have hq := rankFour_unnormalized_bound (n + 1 + a) hnext w
      (fun i j hij => hvo (by exact hij)) (fun i => hvn _)
      (by rw [hws]; positivity) (by rw [hb]; exact h1) (by rw [hb]; exact h2)
      (hmass.mpr h4)
    rw [hwq, hws] at hq
    have hs := insertion_scalar ((n : ℝ) + 17) a t hN (by exact_mod_cast ha) ht0
      (by simpa only [add_assoc, show (17 : ℝ) + 2 = 19 by norm_num] using hsmall)
    have hendpoint : purityBound (n + 1 + a + 16) = scalarF ((n : ℝ) + 17 + a) := by
      unfold purityBound scalarF
      push_cast
      congr 1 <;> ring
    rw [hendpoint] at hq
    rw [hcurrent]
    linarith
  · have hlarge : 1 / ((n : ℝ) + 19) ≤ t := le_of_lt (lt_of_not_ge hsmall)
    have ht1 : t < 1 := by
      change ((n : ℝ) + 13) * t ≤ 1 at hcap
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ n by linarith) ht0]
    let v := rankFourDelete n l
    have hvb := rankFourDelete_boundary n l
    obtain ⟨hb, hmass⟩ := rankFour_preservation (n + 1) n l v hvb
    have hvs : ∑ i, v i = 1 - t := by
      have h := sum_rankFourDelete n l id
      dsimp [id] at h
      rw [ht] at h
      linarith
    have hvq : ∑ i, (v i) ^ 2 = (∑ i, (l i) ^ 2) - t ^ 2 := by
      have h := sum_rankFourDelete n l (fun x => x ^ 2)
      linarith
    have hq := rankFour_unnormalized_bound n hprev v
      (fun i j hij => ho ((Fin.strictMono_succAbove (rankFourMiddle (n + 1))).monotone hij))
      (fun i => hp _) (by rw [hvs]; linarith)
      (by rw [hb]; exact h1) (by rw [hb]; exact h2) (hmass.mpr h4)
    rw [hvs, hvq] at hq
    have hs := deletion_scalar ((n : ℝ) + 17) 4 t hN (by linarith)
      (by nlinarith [sq_nonneg ((n : ℝ) - 8)])
      (by simpa only [add_assoc, show (17 : ℝ) + 2 = 19 by norm_num] using hlarge)
      (by convert hcap using 1 <;> dsimp [t] <;> ring)
    have hendpoint : purityBound (n + 16) = scalarF (((n : ℝ) + 17) - 1) := by
      unfold purityBound scalarF
      push_cast
      congr 1 <;> ring
    rw [hendpoint] at hq
    rw [hcurrent]
    linarith

private theorem rankFour_base24 : RankFourSpectralBound 8 := by
  intro l ho hn ht h1 h2 _
  have hb : boundaryValues (8 + 7) l = QutritSpectralReduction.boundaryValues 5 l := by
    funext q
    fin_cases q <;> norm_num [boundaryValues, boundaryIndex, QutritSpectralReduction.boundaryValues]
  rw [hb] at h1 h2
  convert QutritN8PurityBound.certificate_bound l ho (hn 23) ht h1 h2 using 1 <;>
    norm_num [purityBound]

/-
proof_shape: rank_four_endpoint_interval: content
admission_basis: escape-witness
escape_witness: Induction changes dimension by actual coordinate surgery;
the length-24 base is the existing certificate, and the arbitrary upper
endpoint remains a premise on the same actual spectral constraints.
-/
/-- A bound at any endpoint `M+16 >= 24` fills the entire interval from 24 to it. -/
theorem rank_four_endpoint_interval (M : ℕ) (_hM : 8 ≤ M)
    (hend : RankFourSpectralBound M) :
    ∀ n : ℕ, 8 ≤ n → n ≤ M →
    ∀ l : Fin (n + 16) → ℝ, Antitone l → (∀ i, 0 ≤ l i) → (∑ i, l i) = 1 →
    (K1 (boundaryValues (n + 7) l)).PosSemidef →
    (K2 (boundaryValues (n + 7) l)).PosSemidef →
    UniformRankFourNecessary.sumFirst 6 l ≤ UniformRankFourNecessary.sumLast 10 l →
    ∑ i, (l i)^2 ≤ purityBound (n + 16) := by
  intro n hn hnM
  change RankFourSpectralBound n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hbase : n = 8
      · subst n; exact rankFour_base24
      by_cases hlast : n = M
      · subst n; exact hend
      have hstep := rank_four_spectral_bound_transfer (n - 1) (M - n)
        (by omega) (by omega) (ih (n - 1) (by omega) (by omega) (by omega))
      have heq : n - 1 + 1 + (M - n) = M := by omega
      rw [heq] at hstep
      have hres : RankFourSpectralBound (n - 1 + 1) := hstep hend
      rw [Nat.sub_add_cancel (show 1 ≤ n by omega)] at hres
      exact hres

#print axioms rank_four_spectral_bound_transfer
#print axioms rank_four_endpoint_interval

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer
