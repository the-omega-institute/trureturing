/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer
   mirror-E: none(waiver:algebraic-spectrum-transfer)
   anchors: []
   utility: none
   digest: Extremal observers transfer purity bounds under explicit caps. -/

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

/-- Actual first `p` and last `q` coordinates of a tuple of length `N`. -/
def observerIndex (p q N : ℕ) (h : p + q ≤ N) (i : Fin (p + q)) : Fin N :=
  if hi : i.val < p then ⟨i.val, by omega⟩
  else ⟨N - (p + q) + i.val, by omega⟩

def observerValues (p q N : ℕ) (h : p + q ≤ N) (l : Fin N → ℝ) :
    Fin (p + q) → ℝ := fun i => l (observerIndex p q N h i)

/-- Positive division preserves the entire boundary condition in both directions. -/
def PositiveScaleInvariant {d : ℕ} (C : (Fin d → ℝ) → Prop) : Prop :=
  ∀ (b : Fin d → ℝ) (s : ℝ), 0 < s → (C (fun i => b i / s) ↔ C b)

/-- Universal purity bound on the specified actual extremal observer. -/
def ObserverBound (p q : ℕ) (C : (Fin (p + q) → ℝ) → Prop) (N : ℕ) : Prop :=
  ∀ (h : p + q ≤ N) (l : Fin N → ℝ), Antitone l → (∀ i, 0 ≤ l i) →
    (∑ i, l i) = 1 → C (observerValues p q N h l) →
      ∑ i, (l i) ^ 2 ≤ purityBound N

private def cut (p q n : ℕ) : Fin (p + q + n + 1) := ⟨p + n, by omega⟩

private def insertOne (p q n : ℕ) (l : Fin (p + q + n + 1) → ℝ) :
    Fin (p + q + n + 2) → ℝ :=
  Fin.insertNth ⟨p + n, by omega⟩ (l (cut p q n)) l

private def deleteOne (p q n : ℕ) (l : Fin (p + q + n + 1) → ℝ) :
    Fin (p + q + n) → ℝ := Fin.removeNth (cut p q n) l

private theorem insertOne_order (p q n : ℕ) (l : Fin (p + q + n + 1) → ℝ)
    (ho : Antitone l) : Antitone (insertOne p q n l) := by
  by_cases hz : p + n = 0
  · have hi : (⟨p + n, by omega⟩ : Fin (p + q + n + 2)) = 0 := Fin.ext hz
    have hj : cut p q n = 0 := Fin.ext hz
    have hm : @Monotone (Fin (p + q + n + 2)) ℝᵒᵈ _ _
        (Fin.insertNth 0 (l 0) l) :=
      Fin.insertNth_zero_monotone (α := ℝᵒᵈ) ho (l 0) le_rfl
    change Antitone (Fin.insertNth _ _ _)
    rw [hi, hj]
    exact hm
  · have hmon : @Monotone (Fin (p + q + n + 2)) ℝᵒᵈ _ _
        (Fin.insertNth (⟨p + n, by omega⟩ : Fin (p + q + n + 2))
          (l (cut p q n)) l) := by
      convert (Fin.insertNth_monotone (α := ℝᵒᵈ)
        (f := fun i => (l i : ℝᵒᵈ)) ho
        (⟨p + n - 1, by omega⟩ : Fin (p + q + n)) (l (cut p q n))
        (ho (by change p + n - 1 ≤ p + n; omega))
        (by apply le_of_eq; congr 1; apply Fin.ext; dsimp [cut]; omega)) using 1
      congr 1
      apply Fin.ext
      simp
      omega
    exact hmon

private theorem insertOne_nonneg (p q n : ℕ) (l : Fin (p + q + n + 1) → ℝ)
    (hn : ∀ i, 0 ≤ l i) : ∀ i, 0 ≤ insertOne p q n l i := by
  intro i
  induction i using Fin.succAboveCases (⟨p + n, by omega⟩ : Fin (p + q + n + 2))
  · simpa [insertOne] using hn (cut p q n)
  · simpa [insertOne] using hn _

private theorem insertOne_cut (p q n : ℕ) (l : Fin (p + q + n + 1) → ℝ) :
    insertOne p q n l (cut p q (n + 1)) = l (cut p q n) := by
  have hi : cut p q (n + 1) =
      (⟨p + n, by omega⟩ : Fin (p + q + n + 2)).succAbove (cut p q n) := by
    apply Fin.ext
    simp [cut, Fin.succAbove]
    omega
  rw [hi]
  exact Fin.insertNth_apply_succAbove _ _ _ _

private theorem insertOne_boundary (p q n : ℕ) (l : Fin (p + q + n + 1) → ℝ) :
    observerValues p q (p + q + n + 2) (by omega) (insertOne p q n l) =
      observerValues p q (p + q + n + 1) (by omega) l := by
  funext i
  have hi : observerIndex p q (p + q + n + 2) (by omega) i =
      (⟨p + n, by omega⟩ : Fin (p + q + n + 2)).succAbove
        (observerIndex p q (p + q + n + 1) (by omega) i) := by
    apply Fin.ext
    dsimp [observerIndex, Fin.succAbove]
    split_ifs <;> simp_all <;> omega
  change insertOne p q n l _ = l _
  rw [hi]
  exact Fin.insertNth_apply_succAbove _ _ _ _

private theorem sum_insertOne (p q n : ℕ) (l : Fin (p + q + n + 1) → ℝ)
    (F : ℝ → ℝ) :
    ∑ i, F (insertOne p q n l i) = F (l (cut p q n)) + ∑ i, F (l i) := by
  rw [Fin.sum_univ_succAbove _ (⟨p + n, by omega⟩ : Fin (p + q + n + 2))]
  simp [insertOne]

private theorem insert_copies (a p q n : ℕ) (l : Fin (p + q + n + 1) → ℝ)
    (ho : Antitone l) (hp : ∀ i, 0 ≤ l i) :
    ∃ v : Fin (p + q + n + 1 + a) → ℝ, Antitone v ∧ (∀ i, 0 ≤ v i) ∧
      observerValues p q (p + q + n + 1 + a) (by omega) v =
        observerValues p q (p + q + n + 1) (by omega) l ∧
      (∑ i, v i) = (∑ i, l i) + (a : ℝ) * l (cut p q n) ∧
      (∑ i, (v i) ^ 2) = (∑ i, (l i) ^ 2) + (a : ℝ) * (l (cut p q n)) ^ 2 := by
  induction a generalizing n with
  | zero => refine ⟨l, ho, hp, ?_, ?_, ?_⟩ <;> simp
  | succ a ih =>
      obtain ⟨v, hvo, hvp, hvb, hvs, hvq⟩ := ih (n + 1)
        (insertOne p q n l) (insertOne_order p q n l ho) (insertOne_nonneg p q n l hp)
      have hdim : p + q + (n + 1) + 1 + a = p + q + n + 1 + (a + 1) := by omega
      let w : Fin (p + q + n + 1 + (a + 1)) → ℝ := fun i => v (Fin.cast hdim.symm i)
      have hwF (F : ℝ → ℝ) : (∑ i, F (w i)) = ∑ i, F (v i) :=
        Fin.sum_congr' (fun i => F (v i)) hdim.symm
      refine ⟨w, ?_, ?_, ?_, ?_, ?_⟩
      · intro i j hij; exact hvo (by exact hij)
      · intro i; exact hvp _
      · have hb := insertOne_boundary p q n l
        funext i
        have h := congrFun (hvb.trans hb) i
        change v _ = _ at h
        change v _ = _
        convert h using 1
        congr 1
        apply Fin.ext
        simp only [observerIndex, Fin.val_cast]
        split_ifs <;> simp_all <;> omega
      · have hw := hwF id
        simp only [id_eq] at hw
        have hi := sum_insertOne p q n l id
        simp only [id_eq] at hi
        rw [hw, hvs]
        change (∑ i : Fin (p + q + n + 2), insertOne p q n l i) +
          (a : ℝ) * insertOne p q n l (cut p q (n + 1)) = _
        rw [hi, insertOne_cut]
        push_cast
        ring
      · rw [hwF (fun x => x ^ 2), hvq]
        change (∑ i : Fin (p + q + n + 2), (insertOne p q n l i) ^ 2) +
          (a : ℝ) * (insertOne p q n l (cut p q (n + 1))) ^ 2 = _
        rw [sum_insertOne p q n l (fun x => x ^ 2), insertOne_cut]
        push_cast
        ring

private theorem deleteOne_boundary (p q n : ℕ) (l : Fin (p + q + n + 1) → ℝ) :
    observerValues p q (p + q + n) (by omega) (deleteOne p q n l) =
      observerValues p q (p + q + n + 1) (by omega) l := by
  funext i
  change l ((cut p q n).succAbove (observerIndex p q (p + q + n) (by omega) i)) = l _
  congr 1
  apply Fin.ext
  dsimp [cut, observerIndex, Fin.succAbove]
  split_ifs <;> simp_all <;> omega

private theorem sum_deleteOne (p q n : ℕ) (l : Fin (p + q + n + 1) → ℝ)
    (F : ℝ → ℝ) :
    F (l (cut p q n)) + ∑ i, F (deleteOne p q n l i) = ∑ i, F (l i) :=
  Fin.add_sum_removeNth (cut p q n) (fun i => F (l i))

private theorem observer_unnormalized (p q N : ℕ)
    (C : (Fin (p + q) → ℝ) → Prop) (hscale : PositiveScaleInvariant C)
    (hb : ObserverBound p q C N) (h : p + q ≤ N)
    (l : Fin N → ℝ) (ho : Antitone l) (hn : ∀ i, 0 ≤ l i)
    (hs : 0 < ∑ i, l i) (hc : C (observerValues p q N h l)) :
    ∑ i, (l i) ^ 2 ≤ purityBound N * (∑ i, l i) ^ 2 := by
  let s := ∑ i, l i
  have hs' : 0 < s := hs
  have hp := hb h (fun i => l i / s)
    (fun i j hij => div_le_div_of_nonneg_right (ho hij) hs'.le)
    (fun i => div_nonneg (hn i) hs'.le)
    (by rw [← Finset.sum_div]; exact div_self hs'.ne')
    ((hscale (observerValues p q N h l) s hs').mpr hc)
  simp_rw [div_pow] at hp
  rw [← Finset.sum_div] at hp
  exact (div_le_iff₀ (sq_pos_of_pos hs')).mp hp

private theorem observer_mass_cap (p q n : ℕ) (l : Fin (p + q + n + 1) → ℝ)
    (ho : Antitone l) (ht : ∑ i, l i = 1)
    (hbalance : (∑ i : Fin p, l ⟨i.val, by omega⟩) ≤
      ∑ i : Fin q, l ⟨p + n + 1 + i.val, by omega⟩) :
    ((p + q + n + 1 : ℕ) - ((q : ℝ) - p)) * l (cut p q n) ≤ 1 := by
  let t := l (cut p q n)
  have htop : (p : ℝ) * t ≤ ∑ i : Fin p, l ⟨i.val, by omega⟩ := by
    calc
      _ = ∑ _i : Fin p, t := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => ho (by change i.val ≤ p + n; omega)
  have hprefix : ((p + n + 1 : ℕ) : ℝ) * t ≤
      ∑ i : Fin (p + n + 1), l ⟨i.val, by omega⟩ := by
    calc
      _ = ∑ _i : Fin (p + n + 1), t := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => ho (by change i.val ≤ p + n; omega)
  have htotal : (∑ i : Fin (p + n + 1 + q), l ⟨i.val, by omega⟩) = 1 := by
    convert ht using 1
    exact Fin.sum_congr' l (by omega)
  rw [Fin.sum_univ_add] at htotal
  change (∑ i : Fin (p + n + 1), l ⟨i.val, by omega⟩) +
    (∑ i : Fin q, l ⟨p + n + 1 + i.val, by omega⟩) = 1 at htotal
  push_cast at hprefix ⊢
  dsimp [t] at htop hprefix
  linarith

private theorem K1_div (b : Fin 9 → ℝ) (s : ℝ) :
    K1 (fun q => b q / s) = (1 / s) • K1 b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [K1, Matrix.smul_apply] <;> ring

private theorem K2_div (b : Fin 9 → ℝ) (s : ℝ) :
    K2 (fun q => b q / s) = (1 / s) • K2 b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [K2, Matrix.smul_apply] <;> ring

private theorem middle_cap (n : ℕ) (l : Fin (n + 10) → ℝ)
    (ho : Antitone l) (ht : ∑ i, l i = 1)
    (h1 : (K1 (boundaryValues (n + 1) l)).PosSemidef) :
    ((n : ℝ) + 7) * l (middle (n + 1)) ≤ 1 := by
  let B := ∑ j : Fin 6, l ⟨n + 4 + j.val, by omega⟩
  let T := l ⟨0, by omega⟩ + l ⟨1, by omega⟩ + l ⟨2, by omega⟩
  have hquad := h1.dotProduct_mulVec_nonneg (![1, 1, 1] : Fin 3 → ℝ)
  have hTB : T ≤ B := by
    dsimp [T, B]
    norm_num [K1, boundaryValues, boundaryIndex, dotProduct, Matrix.mulVec,
      Fin.sum_univ_succ, Nat.add_assoc] at hquad ⊢
    linarith
  let w : Fin (3 + 6 + n + 1) → ℝ := fun i => l ⟨i.val, by omega⟩
  have hwo : Antitone w := fun i j hij => ho (by exact hij)
  have hwt : ∑ i, w i = 1 := by
    exact (Fin.sum_congr' l (by omega)).trans ht
  have hbal : (∑ i : Fin 3, w ⟨i.val, by omega⟩) ≤
      ∑ i : Fin 6, w ⟨3 + n + 1 + i.val, by omega⟩ := by
    simpa [T, B, w, Fin.sum_univ_succ, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc, add_assoc] using hTB
  have hh := observer_mass_cap 3 6 n w hwo hwt hbal
  convert hh using 1 <;> dsimp [w, cut, middle] <;> push_cast <;> try ring

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


/- proof_shape: observer_bound_transfer: content
   escape_witness: insert_copies constructs ordered tuples preserving the actual
     extremal observer and both moments for arbitrary p and q; deleteOne removes
     the original coordinate, and observer_unnormalized normalizes these same tuples.
   admission_basis: escape-witness
   utility: not-applicable(kind=none); structural inference, with no finite
     certificate, enumeration, checker or numerical premise discharge.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17734
-/
/-- Extremal-observer transfer with a supplied actual-coordinate cap.
Here `N = p+q+n+1`, the actual deleted index is `N-q-1 = p+n`,
and `kappa` is real: in mass-balance applications it is `(q:ℝ)-p`.
The strict mass bound and the polynomial guard are both required. -/
theorem observer_bound_transfer (p q n a : ℕ)
    (C : (Fin (p + q) → ℝ) → Prop) (kappa : ℝ)
    (hscale : PositiveScaleInvariant C) (ha : 1 ≤ a)
    (hN : 10 ≤ p + q + n + 1)
    (hC : 1 < ((p + q + n + 1 : ℕ) : ℝ) - kappa)
    (hguard : 0 ≤ (10 - kappa) * ((p + q + n + 1 : ℕ) : ℝ) ^ 2 +
      (6 - 15 * kappa) * ((p + q + n + 1 : ℕ) : ℝ) - 20 * kappa - 16)
    (hcap : ∀ (l : Fin (p + q + n + 1) → ℝ), Antitone l →
      (∀ i, 0 ≤ l i) → (∑ i, l i) = 1 →
      C (observerValues p q (p + q + n + 1) (by omega) l) →
      (((p + q + n + 1 : ℕ) : ℝ) - kappa) * l ⟨p + n, by omega⟩ ≤ 1)
    (hprev : ObserverBound p q C (p + q + n))
    (hnext : ObserverBound p q C (p + q + n + 1 + a)) :
    ObserverBound p q C (p + q + n + 1) := by
  intro h l ho hn ht hc
  let N : ℝ := ((p + q + n + 1 : ℕ) : ℝ)
  let t := l (cut p q n)
  have ht0 : 0 ≤ t := hn _
  have hNt : 10 ≤ N := by dsimp [N]; exact_mod_cast hN
  have hct := hcap l ho hn ht hc
  have hcurrent : purityBound (p + q + n + 1) = scalarF N := rfl
  by_cases hsmall : t ≤ 1 / (N + 2)
  · obtain ⟨v, hvo, hvn, hvb, hvs, hvq⟩ := insert_copies a p q n l ho hn
    have hvs' : ∑ i, v i = 1 + (a : ℝ) * t := by rw [hvs, ht]
    have hp := observer_unnormalized p q (p + q + n + 1 + a) C hscale hnext
      (by omega) v hvo hvn (by rw [hvs']; positivity) (by rw [hvb]; exact hc)
    rw [hvq, hvs'] at hp
    have hs := insertion_scalar N a t hNt (by exact_mod_cast ha) ht0 hsmall
    have hendpoint : purityBound (p + q + n + 1 + a) = scalarF (N + a) := by
      simp only [purityBound, scalarF, N, Nat.cast_add]
    rw [hendpoint] at hp
    rw [hcurrent]
    change ∑ i, (l i) ^ 2 ≤ scalarF N
    change _ + (a : ℝ) * t ^ 2 ≤ _ at hp
    linarith
  · have hlarge : 1 / (N + 2) ≤ t := le_of_lt (lt_of_not_ge hsmall)
    have ht1 : t < 1 := by
      have hc0 : 0 < N - kappa := by dsimp [N]; linarith
      have hle : t ≤ 1 / (N - kappa) :=
        (le_div_iff₀ hc0).mpr (by simpa [N, t, cut, mul_comm] using hct)
      exact lt_of_le_of_lt hle ((div_lt_one hc0).mpr hC)
    let v := deleteOne p q n l
    have hvb : observerValues p q (p + q + n) (by omega) v =
        observerValues p q (p + q + n + 1) h l := deleteOne_boundary p q n l
    have hvs : ∑ i, v i = 1 - t := by
      have hs := sum_deleteOne p q n l id
      simp only [id_eq] at hs
      rw [ht] at hs
      change t + _ = 1 at hs
      linarith
    have hvq : ∑ i, (v i) ^ 2 = (∑ i, (l i) ^ 2) - t ^ 2 := by
      have hs := sum_deleteOne p q n l (fun x => x ^ 2)
      change t ^ 2 + _ = _ at hs
      linarith
    have hp := observer_unnormalized p q (p + q + n) C hscale hprev (by omega) v
      (fun i j hij => ho ((Fin.strictMono_succAbove (cut p q n)).monotone hij))
      (fun i => hn _) (by rw [hvs]; linarith) (by rw [hvb]; exact hc)
    rw [hvs, hvq] at hp
    have hs := deletion_scalar N kappa t hNt (by dsimp [N]; linarith)
      hguard hlarge (by simpa [N, t, cut] using hct)
    have hendpoint : purityBound (p + q + n) = scalarF (N - 1) := by
      simp only [purityBound, scalarF, N, Nat.cast_add, Nat.cast_one]
      congr 1 <;> ring
    rw [hendpoint] at hp
    rw [hcurrent]
    linarith

private theorem rank_three_observer (n : ℕ) (l : Fin (n + 9) → ℝ) :
    observerValues 3 6 (n + 9) (by omega) l = boundaryValues n l := by
  rfl

private def RankThreeBoundary (b : Fin 9 → ℝ) : Prop :=
  (K1 b).PosSemidef ∧ (K2 b).PosSemidef

private theorem rank_three_scaling : PositiveScaleInvariant RankThreeBoundary := by
  intro b s hs
  constructor
  · intro hb
    have h1 := hb.1.smul hs.le
    have h2 := hb.2.smul hs.le
    rw [K1_div] at h1
    rw [K2_div] at h2
    simpa [RankThreeBoundary, smul_smul, hs.ne'] using And.intro h1 h2
  · intro hb
    constructor
    · rw [K1_div]; exact hb.1.smul (by positivity)
    · rw [K2_div]; exact hb.2.smul (by positivity)

private theorem rank_three_bound (n : ℕ) :
    ObserverBound 3 6 RankThreeBoundary (n + 9) ↔ SpectralBound n := by
  constructor
  · intro hb l ho hn ht h1 h2
    exact hb (by omega) l ho hn ht (by rw [rank_three_observer]; exact ⟨h1, h2⟩)
  · intro hb h l ho hn ht hc
    rw [rank_three_observer] at hc
    exact hb l ho hn ht hc.1 hc.2

/- proof_shape: spectral_bound_transfer: bind-only
   consumers: DimensionTwentySpectralPurityBound.intermediate_nineteen,
     DimensionTwentySpectralPurityBound.spectral_purity_bound
   consumer direction: those declarations use spectral_bound_transfer.
   escape_witness: none; the original complete specialization is preserved.
-/
/-- For `N = n + 10`, the original rank-three spectral relaxation transfers
from `N-1` and `N+a` to `N`, including all ties and zero coordinates. -/
theorem spectral_bound_transfer (n a : ℕ) (ha : 1 ≤ a)
    (hprev : SpectralBound n) (hnext : SpectralBound (n + 1 + a)) :
    SpectralBound (n + 1) := by
  have hprior : ObserverBound 3 6 RankThreeBoundary (3 + 6 + n) := by
    convert (rank_three_bound n).mpr hprev using 1 <;> omega
  have hafter : ObserverBound 3 6 RankThreeBoundary (3 + 6 + n + 1 + a) := by
    convert (rank_three_bound (n + 1 + a)).mpr hnext using 1 <;> omega
  have htransfer := observer_bound_transfer 3 6 n a RankThreeBoundary 3 rank_three_scaling ha
    (by omega) (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]) (by push_cast; nlinarith [sq_nonneg (n : ℝ)])
    (by
      intro l ho hn ht hc
      let w : Fin (n + 10) → ℝ := fun i => l ⟨i.val, by omega⟩
      have hwo : Antitone w := fun i j hij => ho (by exact hij)
      have hwt : ∑ i, w i = 1 := by
        have he : ∑ i, w i = ∑ i, l i := Fin.sum_congr' l (by omega)
        exact he.trans ht
      have hwb : boundaryValues (n + 1) w =
          observerValues 3 6 (3 + 6 + n + 1) (by omega) l := by
        funext i
        dsimp [boundaryValues, boundaryIndex, observerValues, observerIndex, w]
        congr 1
        apply Fin.ext
        split_ifs <;> simp_all <;> omega
      have hm := middle_cap n w hwo hwt (by rw [hwb]; exact hc.1)
      convert hm using 1 <;> dsimp [w, middle] <;> push_cast <;> try ring)
    hprior hafter
  apply (rank_three_bound (n + 1)).mp
  convert htransfer using 1 <;> omega

#print axioms observer_bound_transfer
#print axioms spectral_bound_transfer

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer
