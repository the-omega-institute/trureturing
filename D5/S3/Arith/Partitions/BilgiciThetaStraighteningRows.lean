/- GID: D5/S3/Arith/Partitions/BilgiciThetaStraighteningRows
   generality: I
   mirror-B: D5/B/S3/Arith/Partitions/BilgiciThetaStraighteningRows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local theta relations and reductions for concentrated multiplicities. -/

import D5.S3.Arith.Partitions.BilgiciThetaStraighteningRank

/-! Local theta relations and reductions for concentrated multiplicities. -/

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening
open D5.S3.Arith.Partitions.BilgiciThetaStructural

private def paperWord (digits : List ℕ) : Word := digits.map (fun i => Fin.ofNat 9 (i-1))

private theorem evalRaw_to (m : List K) (j : ℕ) (n : Word) (c : K)
    (hp : (scaleWord (2^j) (absWord m)).Perm n)
    (hc : coeff m * scaleCoeff j (absWord m) = c) :
    evalRaw m = c • evalWord n := by
  rw [evalRaw_abs, evalWord_power j, smul_smul, hc, evalWord_perm hp]

def baseA : Word := paperWord [1, 1, 1, 3, 3, 5, 7]
def baseB : Word := paperWord [1, 1, 2, 2, 5, 6, 9]
def baseC : Word := paperWord [1, 1, 2, 3, 7, 8, 9]
def baseD : Word := paperWord [1, 1, 3, 4, 5, 6, 8]
def wordE : Word := paperWord [1, 1, 4, 5, 6, 7, 9]
def wordF : Word := paperWord [1, 1, 2, 4, 6, 7, 8]
def wordG : Word := paperWord [1, 1, 2, 3, 3, 4, 6]
def wordH : Word := paperWord [1, 1, 3, 3, 5, 8, 9]
def wordI : Word := paperWord [1, 1, 2, 2, 4, 8, 9]
def wordJ : Word := paperWord [1, 1, 2, 2, 4, 5, 5]
private def wordU : Word := paperWord [1, 1, 1, 2, 4, 6, 6]
private def wordV : Word := paperWord [1, 1, 1, 5, 7, 7, 8]
def wordK : Word := paperWord [1, 1, 3, 6, 7, 7, 8]
def wordL : Word := paperWord [1, 4, 4, 8, 8, 9, 9]
def wordM : Word := paperWord [1, 2, 2, 6, 6, 8, 8]
def wordN : Word := paperWord [1, 5, 5, 6, 6, 9, 9]
def rootR1 : Word := paperWord [1, 1, 1, 1, 1, 3, 9]
def rootR2 : Word := paperWord [1, 1, 1, 4, 4, 4, 5]
def rootR3 : Word := paperWord [1, 1, 2, 3, 5, 5, 7]
def rootR4 : Word := paperWord [1, 1, 1, 2, 3, 4, 5]
def paper1 : Word := paperWord [5, 8, 9, 9, 9, 9, 9]
def paper2 : Word := paperWord [3, 7, 7, 7, 9, 9, 9]
def paper3 : Word := paperWord [1, 6, 7, 7, 8, 9, 9]
def paper4 : Word := paperWord [1, 2, 7, 8, 9, 9, 9]
def wordB7 : Word := paperWord [1, 1, 5, 7, 8, 8, 9]

theorem relF : evalWord wordF = (10 : K) • evalWord baseC := by
  have h0 : evalRaw (row 1 6 3 5 (paperWord [1, 6, 7])) = (8 : K) • evalWord baseC :=
    evalRaw_to (row 1 6 3 5 (paperWord [1, 6, 7])) 3 baseC 8 (by decide) (by decide)
  have h1 : evalRaw (row 1 5 3 6 (paperWord [1, 6, 7])) = (17 : K) • evalWord baseC :=
    evalRaw_to (row 1 5 3 6 (paperWord [1, 6, 7])) 4 baseC 17 (by decide) (by decide)
  have h2 : evalRaw (row 1 3 5 6 (paperWord [1, 6, 7])) = (18 : K) • evalWord wordF :=
    evalRaw_to (row 1 3 5 6 (paperWord [1, 6, 7])) 0 wordF 18 (by decide) (by decide)
  have h := theta_annihilated 1 3 5 6 (paperWord [1, 6, 7])
  rw [h0, h1, h2] at h
  linear_combination (norm := skip) (18 : K) • h
  match_scalars
  all_goals decide

theorem relE : evalWord wordE = (18 : K) • evalWord baseC + (11 : K) • evalWord baseD := by
  have h0 : evalRaw (row 1 5 2 3 (paperWord [1, 7, 9])) = (1 : K) • evalWord wordE :=
    evalRaw_to (row 1 5 2 3 (paperWord [1, 7, 9])) 0 wordE 1 (by decide) (by decide)
  have h1 : evalRaw (row 1 3 2 5 (paperWord [1, 7, 9])) = (11 : K) • evalWord baseD :=
    evalRaw_to (row 1 3 2 5 (paperWord [1, 7, 9])) 3 baseD 11 (by decide) (by decide)
  have h2 : evalRaw (row 1 2 3 5 (paperWord [1, 7, 9])) = (1 : K) • evalWord baseC :=
    evalRaw_to (row 1 2 3 5 (paperWord [1, 7, 9])) 0 baseC 1 (by decide) (by decide)
  have h := theta_annihilated 1 2 3 5 (paperWord [1, 7, 9])
  rw [h0, h1, h2] at h
  linear_combination (norm := skip) (1 : K) • h
  match_scalars
  all_goals decide

theorem relI : evalWord wordI = (15 : K) • evalWord wordE + (14 : K) • evalWord wordF := by
  have h0 : evalRaw (row 1 6 3 5 (paperWord [1, 2, 9])) = (15 : K) • evalWord wordE :=
    evalRaw_to (row 1 6 3 5 (paperWord [1, 2, 9])) 8 wordE 15 (by decide) (by decide)
  have h1 : evalRaw (row 1 5 3 6 (paperWord [1, 2, 9])) = (5 : K) • evalWord wordF :=
    evalRaw_to (row 1 5 3 6 (paperWord [1, 2, 9])) 1 wordF 5 (by decide) (by decide)
  have h2 : evalRaw (row 1 3 5 6 (paperWord [1, 2, 9])) = (18 : K) • evalWord wordI :=
    evalRaw_to (row 1 3 5 6 (paperWord [1, 2, 9])) 0 wordI 18 (by decide) (by decide)
  have h := theta_annihilated 1 3 5 6 (paperWord [1, 2, 9])
  rw [h0, h1, h2] at h
  linear_combination (norm := skip) (18 : K) • h
  match_scalars
  all_goals decide

theorem relR3 : evalWord rootR3 = (13 : K) • evalWord wordF + (9 : K) • evalWord baseD := by
  have h0 : evalRaw (row 1 9 6 8 (paperWord [1, 3, 5])) = (13 : K) • evalWord wordF :=
    evalRaw_to (row 1 9 6 8 (paperWord [1, 3, 5])) 2 wordF 13 (by decide) (by decide)
  have h1 : evalRaw (row 1 8 6 9 (paperWord [1, 3, 5])) = (10 : K) • evalWord baseD :=
    evalRaw_to (row 1 8 6 9 (paperWord [1, 3, 5])) 5 baseD 10 (by decide) (by decide)
  have h2 : evalRaw (row 1 6 8 9 (paperWord [1, 3, 5])) = (18 : K) • evalWord rootR3 :=
    evalRaw_to (row 1 6 8 9 (paperWord [1, 3, 5])) 0 rootR3 18 (by decide) (by decide)
  have h := theta_annihilated 1 6 8 9 (paperWord [1, 3, 5])
  rw [h0, h1, h2] at h
  linear_combination (norm := skip) (18 : K) • h
  match_scalars
  all_goals decide

theorem relK : evalWord wordK = (10 : K) • evalWord baseD + (9 : K) • evalWord wordE := by
  have h0 : evalRaw (row 1 7 3 4 (paperWord [1, 3, 7])) = (1 : K) • evalWord wordK :=
    evalRaw_to (row 1 7 3 4 (paperWord [1, 3, 7])) 0 wordK 1 (by decide) (by decide)
  have h1 : evalRaw (row 1 4 3 7 (paperWord [1, 3, 7])) = (10 : K) • evalWord baseD :=
    evalRaw_to (row 1 4 3 7 (paperWord [1, 3, 7])) 5 baseD 10 (by decide) (by decide)
  have h2 : evalRaw (row 1 3 4 7 (paperWord [1, 3, 7])) = (10 : K) • evalWord wordE :=
    evalRaw_to (row 1 3 4 7 (paperWord [1, 3, 7])) 5 wordE 10 (by decide) (by decide)
  have h := theta_annihilated 1 3 4 7 (paperWord [1, 3, 7])
  rw [h0, h1, h2] at h
  linear_combination (norm := skip) (1 : K) • h
  match_scalars
  all_goals decide

theorem relH : evalWord wordH = (14 : K) • evalWord baseB + (5 : K) • evalWord wordF := by
  have h0 : evalRaw (row 1 8 2 3 (paperWord [1, 3, 9])) = (14 : K) • evalWord baseB :=
    evalRaw_to (row 1 8 2 3 (paperWord [1, 3, 9])) 1 baseB 14 (by decide) (by decide)
  have h1 : evalRaw (row 1 3 2 8 (paperWord [1, 3, 9])) = (14 : K) • evalWord wordF :=
    evalRaw_to (row 1 3 2 8 (paperWord [1, 3, 9])) 1 wordF 14 (by decide) (by decide)
  have h2 : evalRaw (row 1 2 3 8 (paperWord [1, 3, 9])) = (18 : K) • evalWord wordH :=
    evalRaw_to (row 1 2 3 8 (paperWord [1, 3, 9])) 0 wordH 18 (by decide) (by decide)
  have h := theta_annihilated 1 2 3 8 (paperWord [1, 3, 9])
  rw [h0, h1, h2] at h
  linear_combination (norm := skip) (18 : K) • h
  match_scalars
  all_goals decide

theorem relG : evalWord wordG = (1 : K) • evalWord baseC + (1 : K) • evalWord baseD := by
  have h0 : evalRaw (row 1 8 3 5 (paperWord [1, 1, 3])) = (1 : K) • evalWord baseC :=
    evalRaw_to (row 1 8 3 5 (paperWord [1, 1, 3])) 0 baseC 1 (by decide) (by decide)
  have h1 : evalRaw (row 1 5 3 8 (paperWord [1, 1, 3])) = (18 : K) • evalWord baseD :=
    evalRaw_to (row 1 5 3 8 (paperWord [1, 1, 3])) 0 baseD 18 (by decide) (by decide)
  have h2 : evalRaw (row 1 3 5 8 (paperWord [1, 1, 3])) = (18 : K) • evalWord wordG :=
    evalRaw_to (row 1 3 5 8 (paperWord [1, 1, 3])) 0 wordG 18 (by decide) (by decide)
  have h := theta_annihilated 1 3 5 8 (paperWord [1, 1, 3])
  rw [h0, h1, h2] at h
  linear_combination (norm := skip) (18 : K) • h
  match_scalars
  all_goals decide

theorem relJ : evalWord wordJ = (3 : K) • evalWord baseB + (14 : K) • evalWord wordF := by
  have h0 : evalRaw (row 0 7 2 6 (paperWord [1, 5, 9])) = (8 : K) • evalWord wordF :=
    evalRaw_to (row 0 7 2 6 (paperWord [1, 5, 9])) 3 wordF 8 (by decide) (by decide)
  have h1 : evalRaw (row 0 6 2 7 (paperWord [1, 5, 9])) = (6 : K) • evalWord wordJ :=
    evalRaw_to (row 0 6 2 7 (paperWord [1, 5, 9])) 2 wordJ 6 (by decide) (by decide)
  have h2 : evalRaw (row 0 2 6 7 (paperWord [1, 5, 9])) = (18 : K) • evalWord baseB :=
    evalRaw_to (row 0 2 6 7 (paperWord [1, 5, 9])) 0 baseB 18 (by decide) (by decide)
  have h := theta_annihilated 0 2 6 7 (paperWord [1, 5, 9])
  rw [h0, h1, h2] at h
  linear_combination (norm := skip) (3 : K) • h
  match_scalars
  all_goals decide

theorem relL : evalWord wordL = (5 : K) • evalWord baseD + (12 : K) • evalWord wordE := by
  have h0 : evalRaw (row 1 9 7 8 (paperWord [4, 8, 9])) = (1 : K) • evalWord wordL :=
    evalRaw_to (row 1 9 7 8 (paperWord [4, 8, 9])) 0 wordL 1 (by decide) (by decide)
  have h1 : evalRaw (row 1 8 7 9 (paperWord [4, 8, 9])) = (5 : K) • evalWord baseD :=
    evalRaw_to (row 1 8 7 9 (paperWord [4, 8, 9])) 1 baseD 5 (by decide) (by decide)
  have h2 : evalRaw (row 1 7 8 9 (paperWord [4, 8, 9])) = (7 : K) • evalWord wordE :=
    evalRaw_to (row 1 7 8 9 (paperWord [4, 8, 9])) 6 wordE 7 (by decide) (by decide)
  have h := theta_annihilated 1 7 8 9 (paperWord [4, 8, 9])
  rw [h0, h1, h2] at h
  linear_combination (norm := skip) (1 : K) • h
  match_scalars
  all_goals decide

theorem relM : evalWord wordM = (12 : K) • evalWord wordE + (4 : K) • evalWord baseD := by
  have h0 : evalRaw (row 1 9 7 8 (paperWord [2, 6, 8])) = (12 : K) • evalWord wordE :=
    evalRaw_to (row 1 9 7 8 (paperWord [2, 6, 8])) 6 wordE 12 (by decide) (by decide)
  have h1 : evalRaw (row 1 8 7 9 (paperWord [2, 6, 8])) = (15 : K) • evalWord baseD :=
    evalRaw_to (row 1 8 7 9 (paperWord [2, 6, 8])) 8 baseD 15 (by decide) (by decide)
  have h2 : evalRaw (row 1 7 8 9 (paperWord [2, 6, 8])) = (18 : K) • evalWord wordM :=
    evalRaw_to (row 1 7 8 9 (paperWord [2, 6, 8])) 0 wordM 18 (by decide) (by decide)
  have h := theta_annihilated 1 7 8 9 (paperWord [2, 6, 8])
  rw [h0, h1, h2] at h
  linear_combination (norm := skip) (18 : K) • h
  match_scalars
  all_goals decide

theorem relR1 : evalWord rootR1 = (1 : K) • evalWord baseA + (18 : K) • evalWord wordU := by
  have h0 : evalRaw (row 0 6 1 3 (paperWord [1, 1, 1])) = (1 : K) • evalWord wordU :=
    evalRaw_to (row 0 6 1 3 (paperWord [1, 1, 1])) 0 wordU 1 (by decide) (by decide)
  have h1 : evalRaw (row 0 3 1 6 (paperWord [1, 1, 1])) = (1 : K) • evalWord baseA :=
    evalRaw_to (row 0 3 1 6 (paperWord [1, 1, 1])) 0 baseA 1 (by decide) (by decide)
  have h2 : evalRaw (row 0 1 3 6 (paperWord [1, 1, 1])) = (1 : K) • evalWord rootR1 :=
    evalRaw_to (row 0 1 3 6 (paperWord [1, 1, 1])) 0 rootR1 1 (by decide) (by decide)
  have h := theta_annihilated 0 1 3 6 (paperWord [1, 1, 1])
  rw [h0, h1, h2] at h
  linear_combination (norm := skip) (1 : K) • h
  match_scalars
  all_goals decide

theorem relU : evalWord wordU = (14 : K) • evalWord wordI + (3 : K) • evalWord wordJ := by
  have h0 : evalRaw (row 0 9 6 8 (paperWord [1, 1, 4])) = (14 : K) • evalWord wordI :=
    evalRaw_to (row 0 9 6 8 (paperWord [1, 1, 4])) 1 wordI 14 (by decide) (by decide)
  have h1 : evalRaw (row 0 8 6 9 (paperWord [1, 1, 4])) = (16 : K) • evalWord wordJ :=
    evalRaw_to (row 0 8 6 9 (paperWord [1, 1, 4])) 7 wordJ 16 (by decide) (by decide)
  have h2 : evalRaw (row 0 6 8 9 (paperWord [1, 1, 4])) = (18 : K) • evalWord wordU :=
    evalRaw_to (row 0 6 8 9 (paperWord [1, 1, 4])) 0 wordU 18 (by decide) (by decide)
  have h := theta_annihilated 0 6 8 9 (paperWord [1, 1, 4])
  rw [h0, h1, h2] at h
  linear_combination (norm := skip) (18 : K) • h
  match_scalars
  all_goals decide

theorem relR2 : evalWord rootR2 = (3 : K) • evalWord wordV + (6 : K) • evalWord wordG := by
  have h0 : evalRaw (row 0 9 1 5 (paperWord [1, 4, 4])) = (3 : K) • evalWord wordV :=
    evalRaw_to (row 0 9 1 5 (paperWord [1, 4, 4])) 7 wordV 3 (by decide) (by decide)
  have h1 : evalRaw (row 0 5 1 9 (paperWord [1, 4, 4])) = (13 : K) • evalWord wordG :=
    evalRaw_to (row 0 5 1 9 (paperWord [1, 4, 4])) 2 wordG 13 (by decide) (by decide)
  have h2 : evalRaw (row 0 1 5 9 (paperWord [1, 4, 4])) = (18 : K) • evalWord rootR2 :=
    evalRaw_to (row 0 1 5 9 (paperWord [1, 4, 4])) 0 rootR2 18 (by decide) (by decide)
  have h := theta_annihilated 0 1 5 9 (paperWord [1, 4, 4])
  rw [h0, h1, h2] at h
  linear_combination (norm := skip) (18 : K) • h
  match_scalars
  all_goals decide

theorem relV : evalWord wordV = (14 : K) • evalWord baseB + (15 : K) • evalWord wordE := by
  have h0 : evalRaw (row 0 9 1 2 (paperWord [1, 5, 7])) = (14 : K) • evalWord baseB :=
    evalRaw_to (row 0 9 1 2 (paperWord [1, 5, 7])) 1 baseB 14 (by decide) (by decide)
  have h1 : evalRaw (row 0 2 1 9 (paperWord [1, 5, 7])) = (4 : K) • evalWord wordE :=
    evalRaw_to (row 0 2 1 9 (paperWord [1, 5, 7])) 8 wordE 4 (by decide) (by decide)
  have h2 : evalRaw (row 0 1 2 9 (paperWord [1, 5, 7])) = (18 : K) • evalWord wordV :=
    evalRaw_to (row 0 1 2 9 (paperWord [1, 5, 7])) 0 wordV 18 (by decide) (by decide)
  have h := theta_annihilated 0 1 2 9 (paperWord [1, 5, 7])
  rw [h0, h1, h2] at h
  linear_combination (norm := skip) (18 : K) • h
  match_scalars
  all_goals decide

theorem relR4 : evalWord rootR4 = (9 : K) • evalWord baseC := by
  have h0 : evalRaw (row 0 8 1 6 (paperWord [1, 3, 4])) = (7 : K) • evalWord baseC :=
    evalRaw_to (row 0 8 1 6 (paperWord [1, 3, 4])) 6 baseC 7 (by decide) (by decide)
  have h1 : evalRaw (row 0 6 1 8 (paperWord [1, 3, 4])) = (17 : K) • evalWord baseC :=
    evalRaw_to (row 0 6 1 8 (paperWord [1, 3, 4])) 4 baseC 17 (by decide) (by decide)
  have h2 : evalRaw (row 0 1 6 8 (paperWord [1, 3, 4])) = (18 : K) • evalWord rootR4 :=
    evalRaw_to (row 0 1 6 8 (paperWord [1, 3, 4])) 0 rootR4 18 (by decide) (by decide)
  have h := theta_annihilated 0 1 6 8 (paperWord [1, 3, 4])
  rw [h0, h1, h2] at h
  linear_combination (norm := skip) (18 : K) • h
  match_scalars
  all_goals decide


end D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening
open D5.S3.Arith.Partitions.BilgiciThetaStructural

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem normalize_at {M : Submodule K A} (m : Word) (a : Fin 9)
    (hs : smaller M m) (hz : centered m = 0)
    (h : ∀ k : K, k ≠ 0 → scaleIndex k a = 0 →
      smaller M (scaleWord k m) → centered (scaleWord k m) = 0 →
      evalWord (scaleWord k m) ∈ M) :
    evalWord m ∈ M := by
  let k : K := (digit a)⁻¹
  have hk : k ≠ 0 := inv_ne_zero (digit_nonzero a)
  obtain ⟨c, hc⟩ := evalWord_scale k hk m
  rw [hc]
  apply M.smul_mem
  apply h k hk (scaleIndex_one k a (inv_mul_cancel₀ (digit_nonzero a)))
    (smaller_scale k hk hs)
  rw [scale_center k hk, hz, mul_zero]

theorem mem_case_perm {M : Submodule K A} {m n : Word} (hp : m.Perm n)
    (hs : smaller M m) (hz : centered m = 0)
    (h : smaller M n → centered n = 0 → evalWord n ∈ M) : evalWord m ∈ M := by
  rw [evalWord_perm hp]
  exact h (smaller_perm hp hs) ((centered_perm hp).symm.trans hz)

macro "perm_counts" : tactic =>
  `(tactic| (apply List.perm_iff_count.mpr; intro i; simp only [List.count_cons, List.count_nil]; omega))


theorem reduce7 {M : Submodule K A} (a : Fin 9) (hd : [a].Nodup)
    (hs : smaller M [a, a, a, a, a, a, a])
    (hz : centered [a, a, a, a, a, a, a] = 0) : evalWord [a, a, a, a, a, a, a] ∈ M := by
  apply normalize_at _ a hs hz
  intro k hk h0 hs' hz'
  have hd' := hd.map (scaleIndex_injective hk)
  simp only [scaleWord, List.map_cons, List.map_nil, h0] at hs' hz' ⊢
  simp only [List.map_cons, List.map_nil, h0] at hd'
  have step (hd : ([0] : Word).Nodup)
    (hz : centered [0, 0, 0, 0, 0, 0, 0] = 0) :
    False := by
    revert hz
    decide
  have h := step  hd' hz'
  exact h.elim

theorem reduce61 {M : Submodule K A} (a b : Fin 9) (hd : [a, b].Nodup)
    (hs : smaller M [a, a, a, a, a, a, b])
    (hz : centered [a, a, a, a, a, a, b] = 0) : evalWord [a, a, a, a, a, a, b] ∈ M := by
  apply normalize_at _ a hs hz
  intro k hk h0 hs' hz'
  have hd' := hd.map (scaleIndex_injective hk)
  simp only [scaleWord, List.map_cons, List.map_nil, h0] at hs' hz' ⊢
  simp only [List.map_cons, List.map_nil, h0] at hd'
  have step (b : Fin 9) (hd : ([0, b] : Word).Nodup)
    (hz : centered [0, 0, 0, 0, 0, 0, b] = 0) :
    False := by
    revert b
    decide
  have h := step (scaleIndex k b) hd' hz'
  exact h.elim

theorem reduce52 {M : Submodule K A} (a b : Fin 9) (hd : [a, b].Nodup)
    (hs : smaller M [a, a, a, a, a, b, b])
    (hz : centered [a, a, a, a, a, b, b] = 0) : evalWord [a, a, a, a, a, b, b] ∈ M := by
  apply normalize_at _ a hs hz
  intro k hk h0 hs' hz'
  have hd' := hd.map (scaleIndex_injective hk)
  simp only [scaleWord, List.map_cons, List.map_nil, h0] at hs' hz' ⊢
  simp only [List.map_cons, List.map_nil, h0] at hd'
  have step (b : Fin 9) (hd : ([0, b] : Word).Nodup)
    (hz : centered [0, 0, 0, 0, 0, b, b] = 0) :
    goodMove 0 0 0 b [0, 0, b] := by
    decide +revert
  have h := step (scaleIndex k b) hd' hz'
  exact goodMove_from_perm (by perm_counts) h hs' rfl hz'

theorem reduce511 {M : Submodule K A} (a b c : Fin 9) (hd : [a, b, c].Nodup)
    (hs : smaller M [a, a, a, a, a, b, c])
    (hz : centered [a, a, a, a, a, b, c] = 0) : evalWord [a, a, a, a, a, b, c] ∈ M := by
  apply normalize_at _ a hs hz
  intro k hk h0 hs' hz'
  have hd' := hd.map (scaleIndex_injective hk)
  simp only [scaleWord, List.map_cons, List.map_nil, h0] at hs' hz' ⊢
  simp only [List.map_cons, List.map_nil, h0] at hd'
  have step (b c : Fin 9) (hd : ([0, b, c] : Word).Nodup)
    (hz : centered [0, 0, 0, 0, 0, b, c] = 0) :
    goodMove 0 0 b c [0, 0, 0] ∨ goodMove 0 0 0 b [0, 0, c] ∨ goodMove 0 0 0 c [0, 0, b] := by
    decide +revert
  have h := step (scaleIndex k b) (scaleIndex k c) hd' hz'
  rcases h with h | h | h
  · exact goodMove_from_perm (by perm_counts) h hs' rfl hz'
  · exact goodMove_from_perm (by perm_counts) h hs' rfl hz'
  · exact goodMove_from_perm (by perm_counts) h hs' rfl hz'

theorem reduce43 {M : Submodule K A} (a b : Fin 9) (hd : [a, b].Nodup)
    (hs : smaller M [a, a, a, a, b, b, b])
    (hz : centered [a, a, a, a, b, b, b] = 0) : evalWord [a, a, a, a, b, b, b] ∈ M := by
  apply normalize_at _ b hs hz
  intro k hk h0 hs' hz'
  have hd' := hd.map (scaleIndex_injective hk)
  simp only [scaleWord, List.map_cons, List.map_nil, h0] at hs' hz' ⊢
  simp only [List.map_cons, List.map_nil, h0] at hd'
  have step (a : Fin 9) (hd : ([a, 0] : Word).Nodup)
    (hz : centered [a, a, a, a, 0, 0, 0] = 0) :
    goodMove 0 0 0 a [a, a, a] := by
    decide +revert
  have h := step (scaleIndex k a) hd' hz'
  exact goodMove_from_perm (by perm_counts) h hs' rfl hz'

theorem reduce421 {M : Submodule K A} (a b c : Fin 9) (hd : [a, b, c].Nodup)
    (hs : smaller M [a, a, a, a, b, b, c])
    (hz : centered [a, a, a, a, b, b, c] = 0) : evalWord [a, a, a, a, b, b, c] ∈ M := by
  apply normalize_at _ a hs hz
  intro k hk h0 hs' hz'
  have hd' := hd.map (scaleIndex_injective hk)
  simp only [scaleWord, List.map_cons, List.map_nil, h0] at hs' hz' ⊢
  simp only [List.map_cons, List.map_nil, h0] at hd'
  have step (b c : Fin 9) (hd : ([0, b, c] : Word).Nodup)
    (hz : centered [0, 0, 0, 0, b, b, c] = 0) :
    goodMove 0 0 b c [0, 0, b] := by
    decide +revert
  have h := step (scaleIndex k b) (scaleIndex k c) hd' hz'
  exact goodMove_from_perm (by perm_counts) h hs' rfl hz'

theorem reduce4111 {M : Submodule K A} (a b c d : Fin 9) (hd : [a, b, c, d].Nodup)
    (hs : smaller M [a, a, a, a, b, c, d])
    (hz : centered [a, a, a, a, b, c, d] = 0) : evalWord [a, a, a, a, b, c, d] ∈ M := by
  apply normalize_at _ a hs hz
  intro k hk h0 hs' hz'
  have hd' := hd.map (scaleIndex_injective hk)
  simp only [scaleWord, List.map_cons, List.map_nil, h0] at hs' hz' ⊢
  simp only [List.map_cons, List.map_nil, h0] at hd'
  have step (b c d : Fin 9) (hd : ([0, b, c, d] : Word).Nodup)
    (hz : centered [0, 0, 0, 0, b, c, d] = 0) :
    goodMove 0 0 b c [0, 0, d] ∨ goodMove 0 0 b d [0, 0, c] ∨ goodMove 0 0 c d [0, 0, b] := by
    fin_cases b <;> decide +revert
  have h := step (scaleIndex k b) (scaleIndex k c) (scaleIndex k d) hd' hz'
  rcases h with h | h | h
  · exact goodMove_from_perm (by perm_counts) h hs' rfl hz'
  · exact goodMove_from_perm (by perm_counts) h hs' rfl hz'
  · exact goodMove_from_perm (by perm_counts) h hs' rfl hz'

theorem reduce331 {M : Submodule K A} (a b c : Fin 9) (hd : [a, b, c].Nodup)
    (hs : smaller M [a, a, a, b, b, b, c])
    (hz : centered [a, a, a, b, b, b, c] = 0) : evalWord [a, a, a, b, b, b, c] ∈ M := by
  apply normalize_at _ a hs hz
  intro k hk h0 hs' hz'
  have hd' := hd.map (scaleIndex_injective hk)
  simp only [scaleWord, List.map_cons, List.map_nil, h0] at hs' hz' ⊢
  simp only [List.map_cons, List.map_nil, h0] at hd'
  have step (b c : Fin 9) (hd : ([0, b, c] : Word).Nodup)
    (hz : centered [0, 0, 0, b, b, b, c] = 0) :
    goodMove 0 0 b c [0, b, b] ∨ goodMove b b 0 c [0, b, 0] := by
    decide +revert
  have h := step (scaleIndex k b) (scaleIndex k c) hd' hz'
  rcases h with h | h
  · exact goodMove_from_perm (by perm_counts) h hs' rfl hz'
  · exact goodMove_from_perm (by perm_counts) h hs' rfl hz'

theorem reduce322 {M : Submodule K A} (a b c : Fin 9) (hd : [a, b, c].Nodup)
    (hs : smaller M [a, a, a, b, b, c, c])
    (hz : centered [a, a, a, b, b, c, c] = 0) : evalWord [a, a, a, b, b, c, c] ∈ M := by
  apply normalize_at _ a hs hz
  intro k hk h0 hs' hz'
  have hd' := hd.map (scaleIndex_injective hk)
  simp only [scaleWord, List.map_cons, List.map_nil, h0] at hs' hz' ⊢
  simp only [List.map_cons, List.map_nil, h0] at hd'
  have step (b c : Fin 9) (hd : ([0, b, c] : Word).Nodup)
    (hz : centered [0, 0, 0, b, b, c, c] = 0) :
    goodMove 0 0 b c [0, b, c] := by
    decide +revert
  have h := step (scaleIndex k b) (scaleIndex k c) hd' hz'
  exact goodMove_from_perm (by perm_counts) h hs' rfl hz'

theorem reduce3211 {M : Submodule K A} (a b c d : Fin 9) (hd : [a, b, c, d].Nodup)
    (ha : evalWord baseA ∈ M) (hs : smaller M [a, a, a, b, b, c, d])
    (hz : centered [a, a, a, b, b, c, d] = 0) : evalWord [a, a, a, b, b, c, d] ∈ M := by
  apply normalize_at _ a hs hz
  intro k hk h0 hs' hz'
  have hd' := hd.map (scaleIndex_injective hk)
  simp only [scaleWord, List.map_cons, List.map_nil, h0] at hs' hz' ⊢
  simp only [List.map_cons, List.map_nil, h0] at hd'
  have step (b c d : Fin 9) (hd : ([0, b, c, d] : Word).Nodup)
    (hz : centered [0, 0, 0, b, b, c, d] = 0) :
    goodMove 0 0 b c [0, b, d] ∨ goodMove 0 0 b d [0, b, c] ∨ goodMove b b 0 c [0, 0, d] ∨ goodMove b b 0 d [0, 0, c] ∨ [0, 0, 0, b, b, c, d].Perm baseA := by
    fin_cases b <;> decide +revert
  have h := step (scaleIndex k b) (scaleIndex k c) (scaleIndex k d) hd' hz'
  rcases h with h | h | h | h | h
  · exact goodMove_from_perm (by perm_counts) h hs' rfl hz'
  · exact goodMove_from_perm (by perm_counts) h hs' rfl hz'
  · exact goodMove_from_perm (by perm_counts) h hs' rfl hz'
  · exact goodMove_from_perm (by perm_counts) h hs' rfl hz'
  · rwa [evalWord_perm h]

theorem reduce31111 {M : Submodule K A} (a b c d e : Fin 9) (hd : [a, b, c, d, e].Nodup)
    (hs : smaller M [a, a, a, b, c, d, e])
    (hz : centered [a, a, a, b, c, d, e] = 0) : evalWord [a, a, a, b, c, d, e] ∈ M := by
  apply normalize_at _ a hs hz
  intro k hk h0 hs' hz'
  have hd' := hd.map (scaleIndex_injective hk)
  simp only [scaleWord, List.map_cons, List.map_nil, h0] at hs' hz' ⊢
  simp only [List.map_cons, List.map_nil, h0] at hd'
  have step (b c d e : Fin 9) (hd : ([0, b, c, d, e] : Word).Nodup)
    (hz : centered [0, 0, 0, b, c, d, e] = 0) :
    goodMove 0 0 b c [0, d, e] ∨ goodMove 0 0 b d [0, c, e] ∨ goodMove 0 0 b e [0, c, d] ∨ goodMove 0 0 c d [0, b, e] ∨ goodMove 0 0 c e [0, b, d] ∨ goodMove 0 0 d e [0, b, c] := by
    fin_cases b <;> decide +revert
  have h := step (scaleIndex k b) (scaleIndex k c) (scaleIndex k d) (scaleIndex k e) hd' hz'
  rcases h with h | h | h | h | h | h
  · exact goodMove_from_perm (by perm_counts) h hs' rfl hz'
  · exact goodMove_from_perm (by perm_counts) h hs' rfl hz'
  · exact goodMove_from_perm (by perm_counts) h hs' rfl hz'
  · exact goodMove_from_perm (by perm_counts) h hs' rfl hz'
  · exact goodMove_from_perm (by perm_counts) h hs' rfl hz'
  · exact goodMove_from_perm (by perm_counts) h hs' rfl hz'


end D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening
