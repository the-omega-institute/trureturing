/- GID: D5/S1/Words/TribonacciAlignedWindows
   generality: G
   mirror-B: D5/B/S1/Words/TribonacciAlignedWindows
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: Uniform odd repetition windows at even starts in the actual Tribonacci word. -/
import D5.S1.Words.MBonacciSentinelDesubstitution

/-! Literal substitution transports a square while preserving its required parity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.TribonacciAlignedWindows

open RankOneMorphismIterationBound (subst image image_add subst_append)
open MBonacciSentinelDesubstitution (phi zero word iterate_prefix word_eq_iterate)

/-- A, B and C are respectively the letters 0, 1 and 2 of Fin 3. -/
abbrev sigma : Fin 3 → List (Fin 3) := phi (by omega : 2 ≤ 3)

/-- The closed, zero-indexed limit word, without a recurrence assumption. -/
abbrev W : ℕ → Fin 3 := word (by omega : 2 ≤ 3)

/-- Length of the actual jth substitution iterate on A. -/
def L (j : ℕ) : ℕ := (image sigma j 0).length

/-- The largest even length not exceeding the actual iterate length. -/
def N (j : ℕ) : ℕ := 2 * (L j / 2)

private theorem subst_upper (w : List (Fin 3)) :
    (subst sigma w).length ≤ 2 * w.length := by
  induction w with
  | nil => simp [subst]
  | cons a w ih =>
    have ha : (sigma a).length ≤ 2 :=
      MBonacciSentinelDesubstitution.phi_len_le (by omega : 2 ≤ 3) a
    simp only [RankOneMorphismIterationBound.subst_cons, List.length_append, List.length_cons]
    omega

private theorem length_step (k : ℕ) : L (k + 1) ≤ 2 * L k := subst_upper _

private theorem length_mono {k j : ℕ} (h : k ≤ j) : L k ≤ L j :=
  (iterate_prefix (by omega : 2 ≤ 3) h).length_le

private theorem length_seven (k : ℕ) : L (k + 7) ≤ 128 * L k := by
  have h0 := length_step k
  have h1 := length_step (k+1)
  have h2 := length_step (k+2)
  have h3 := length_step (k+3)
  have h4 := length_step (k+4)
  have h5 := length_step (k+5)
  have h6 := length_step (k+6)
  simp only [Nat.add_assoc, Nat.reduceAdd] at *
  omega

private theorem four_parity (k : ℕ) :
    ∀ a : Fin 3, (image sigma (4*k) a).length % 2 = 1 := by
  induction k with
  | zero => intro a; rfl
  | succ k ih =>
    intro a
    have h0 := ih 0
    have h1 := ih 1
    have h2 := ih 2
    rw [show 4 * (k+1) = 4*k+4 by omega, image_add]
    have hA : image sigma 4 0 = [0,1,0,2,0,1,0,0,1,0,2,0,1] := by decide
    have hB : image sigma 4 1 = [0,1,0,2,0,1,0,0,1,0,2] := by decide
    have hC : image sigma 4 2 = [0,1,0,2,0,1,0] := by decide
    fin_cases a
    · change (subst (image sigma (4*k)) (image sigma 4 0)).length % 2 = 1
      rw [hA]
      simp only [subst, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append]
      omega
    · change (subst (image sigma (4*k)) (image sigma 4 1)).length % 2 = 1
      rw [hB]
      simp only [subst, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append]
      omega
    · change (subst (image sigma (4*k)) (image sigma 4 2)).length % 2 = 1
      rw [hC]
      simp only [subst, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append]
      omega

private theorem seed (k : ℕ) :
    image sigma (k+4) 0 =
      subst (image sigma k) [0,1,0,2] ++
      subst (image sigma k) [0,1,0] ++
      subst (image sigma k) [0,1,0] ++
      subst (image sigma k) [2,0,1] := by
  rw [image_add]
  have hs : image sigma 4 0 = [0,1,0,2] ++ [0,1,0] ++ [0,1,0] ++ [2,0,1] := by
    decide
  rw [hs]
  simp only [subst_append]

/-- A uniform macroscopic repetition window in every sufficiently long even prefix.
The two repeated blocks are literal factors of the closed word. -/
theorem aligned_windows :
    ∃ K : ℕ, 0 < K ∧ ∃ J : ℕ, 1 ≤ J ∧
      ∀ j : ℕ, J ≤ j → ∃ m s : ℕ,
        3 ≤ m ∧ Odd m ∧ Even s ∧ N j ≤ K*m ∧ s+2*m ≤ N j ∧
        ∀ i : ℕ, i < m-1 → W (s+i+m) = W (s+i) := by
  refine ⟨128, by omega, 4, by omega, ?_⟩
  intro j hj
  let q := (j-4)/4
  let k := 4*q
  have hk : k+4 ≤ j ∧ j ≤ k+7 := by dsimp [k,q]; omega
  let a := image sigma k 0
  let b := image sigma k 1
  let c := image sigma k 2
  let p := a ++ b ++ a ++ c
  let u := a ++ b ++ a
  let t := c ++ a ++ b
  have he : image sigma (k+4) 0 = p ++ u ++ u ++ t := by
    simpa [p,u,t,a,b,c,subst,List.append_assoc] using seed k
  have ha := MBonacciSentinelDesubstitution.image_pos (by omega : 2 ≤ 3) k 0
  have hb := MBonacciSentinelDesubstitution.image_pos (by omega : 2 ≤ 3) k 1
  have hc := MBonacciSentinelDesubstitution.image_pos (by omega : 2 ≤ 3) k 2
  have hpa := four_parity q 0
  have hpb := four_parity q 1
  have hpc := four_parity q 2
  change a.length % 2 = 1 at hpa
  change b.length % 2 = 1 at hpb
  change c.length % 2 = 1 at hpc
  refine ⟨u.length, p.length, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [u,List.length_append]; omega
  · rw [Nat.odd_iff]
    simp only [u,List.length_append]; omega
  · rw [Nat.even_iff]
    simp only [p,List.length_append]; omega
  · have h := le_trans (length_mono hk.2) (length_seven k)
    have hN : N j ≤ L j := by unfold N; omega
    have hm : L k ≤ u.length := by simp [L,u,a]
    omega
  · have hlen : L (k+4) = p.length + u.length + u.length + t.length := by
      simp only [L,he,List.length_append]
    have ht : 1 ≤ t.length := by simp only [t,List.length_append]; omega
    have hmono := length_mono hk.1
    unfold N
    omega
  · intro i hi
    have hlen : L (k+4) = p.length + u.length + u.length + t.length := by
      simp only [L,he,List.length_append]
    have hleft : p.length+i+u.length < (image sigma (k+4) 0).length := by
      change p.length+i+u.length < L (k+4); omega
    have hright : p.length+i < (image sigma (k+4) 0).length := by omega
    change word (by omega : 2 ≤ 3) (p.length+i+u.length) =
      word (by omega : 2 ≤ 3) (p.length+i)
    rw [word_eq_iterate (by omega : 2 ≤ 3) (k+4) _ hleft,
      word_eq_iterate (by omega : 2 ≤ 3) (k+4) _ hright]
    change (image sigma (k+4) 0)[p.length+i+u.length] =
      (image sigma (k+4) 0)[p.length+i]
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem hleft, ← List.getElem?_eq_getElem hright, he]
    have hiu : i < u.length := by omega
    have hpL : ¬ p.length + (i + u.length) < p.length := by omega
    have hpR : ¬ p.length + i < p.length := by omega
    have hu : ¬ i + u.length < u.length := by omega
    simp only [List.append_assoc, List.getElem?_append, Nat.add_assoc, hpL, hpR, hu,
      hiu, if_true, if_false, Nat.add_sub_cancel_left, Nat.add_sub_cancel]

end D5.S1.Words.TribonacciAlignedWindows
