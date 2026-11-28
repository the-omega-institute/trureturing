/- GID: D5/S3/Combinatorics/Graph/Walks/Q61TightWalkPayoff
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/Q61TightWalkPayoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A zero-start free-endpoint payoff lower bound from tight min-plus walks. -/
import D5.S3.Combinatorics.Graph.Walks.Q61CompactAssignmentSlack

/-! A finite-horizon lower bound for the original complete-Bob payoff from a
virtual projective input, with its actual assignment slack. -/

namespace Q61TightWalkPayoff

open Maths MeyerovitchYoungQ61Complete Q61AssignmentGuards Q61CompactAssignmentSlack
open scoped BigOperators

noncomputable section

variable {W V E : Type*} [Fintype W] [Nonempty W]

private theorem endpointUpdate_mono (A : Matrix W W ℝ) : Monotone (endpointUpdate A) := by
  intro x y hxy j
  change endpointUpdate A x j ≤ Finset.univ.inf' Finset.univ_nonempty (fun i => y i + A i j)
  apply Finset.le_inf' Finset.univ_nonempty _
  intro i _
  exact (endpointUpdate_le A x i j).trans (add_le_add (hxy i) le_rfl)

theorem endpointScores_mono (M : E → Matrix W W ℝ) (a : List E) :
    Monotone (fun x => endpointScores M x a) := by
  induction a using List.reverseRecOn with
  | nil => exact monotone_id
  | append_singleton a e ih =>
    intro x y hxy
    simp only [endpointScores_snoc]
    exact endpointUpdate_mono (M e) (ih hxy)

private theorem endpointUpdate_add_const (A : Matrix W W ℝ) (x : W → ℝ) (d : ℝ) :
    endpointUpdate A (fun i => x i + d) = fun j => endpointUpdate A x j + d := by
  funext j
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := W))
    (fun i => x i + A i j)
  change endpointUpdate A x j = x i + A i j at hi
  apply le_antisymm
  · have h := endpointUpdate_le A (fun i => x i + d) i j
    linarith only [hi, h]
  · change endpointUpdate A x j + d ≤
      Finset.univ.inf' Finset.univ_nonempty (fun i => x i + d + A i j)
    apply Finset.le_inf' Finset.univ_nonempty _
    intro k _
    linarith only [endpointUpdate_le A x k j]

theorem endpointScores_add_const (M : E → Matrix W W ℝ) (a : List E)
    (x : W → ℝ) (d : ℝ) :
    endpointScores M (fun i => x i + d) a = fun j => endpointScores M x a j + d := by
  induction a using List.reverseRecOn with
  | nil => rfl
  | append_singleton a e ih =>
    simp only [endpointScores_snoc, ih, endpointUpdate_add_const]

private theorem sum_le_card_sub_one_mul (f : W → ℝ) (k : W) {B : ℝ}
    (hk : f k = 0) (hf : ∀ j, f j ≤ B) :
    (∑ j, f j) ≤ ((Fintype.card W : ℝ) - 1) * B := by
  classical
  have hmem : k ∈ (Finset.univ : Finset W) := Finset.mem_univ k
  have hcardNat : ((Finset.univ : Finset W).erase k).card + 1 = Fintype.card W := by
    simpa only [Finset.card_univ] using Finset.card_erase_add_one hmem
  have hcard : (((Finset.univ : Finset W).erase k).card : ℝ) =
      (Fintype.card W : ℝ) - 1 := by
    have hcast : (((Finset.univ : Finset W).erase k).card : ℝ) + 1 =
        (Fintype.card W : ℝ) := by exact_mod_cast hcardNat
    exact eq_sub_of_add_eq hcast
  calc
    (∑ j, f j) = ∑ j ∈ Finset.univ.erase k, f j := by
      simpa only [hk, add_zero] using (Finset.sum_erase_add _ f hmem).symm
    _ ≤ ∑ _j ∈ Finset.univ.erase k, B := Finset.sum_le_sum fun j _ => hf j
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]

variable (G : EdgeGraph V E) (M : E → Matrix W W ℝ) (rate : ℝ) (H : V → ℝ)

/-- From a projective input, the actual slack reduces the zero-start payoff
bound by its per-Bob-vertex share. Each spread correction charges at most
one copy of `B` to each coordinate other than an attained extremum. -/
theorem matrixMinimum_ge_of_assignmentSlack (o : W) {B : ℝ}
    (hrow : ∀ e i j k, M e i j - M e i k ≤ B)
    {s t : V} (p : G.Walk s t) (x : W → ℝ) (hx : x ∈ projectiveBox o B) :
    (p.length : ℝ) * rate +
        (H s - H t - assignmentSlack M rate H s t p.edges x) / (Fintype.card W : ℝ) -
        2 * (1 - 1 / (Fintype.card W : ℝ)) * B ≤ matrixMinimum M p.edges := by
  let y := endpointScores M x p.edges
  obtain ⟨iMax, _, hiMax⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := W)) x
  obtain ⟨jMin, _, hjMin⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := W)) y
  have hxMax (i : W) : x i ≤ x iMax := by
    rw [← hiMax]
    exact Finset.le_sup' x (Finset.mem_univ i)
  have hyMin (j : W) : y jMin ≤ y j := by
    rw [← hjMin]
    exact Finset.inf'_le y (Finset.mem_univ j)
  change x o = 0 ∧ ∀ i j, x i - x j ≤ B at hx
  have hnorm : Q61CompactAssignmentSlack.normalize o x = x := by
    funext i
    change x i - x o = x i
    rw [hx.1, sub_zero]
  have hxNorm : Q61CompactAssignmentSlack.normalize o x ∈ projectiveBox o B := by
    rw [hnorm]
    exact hx
  have hy : Q61CompactAssignmentSlack.normalize o y ∈ projectiveBox o B :=
    normalize_endpointScores_mem M o hrow p.edges x hxNorm
  change Q61CompactAssignmentSlack.normalize o y o = 0 ∧ ∀ j k, Q61CompactAssignmentSlack.normalize o y j - Q61CompactAssignmentSlack.normalize o y k ≤ B at hy
  have hySpread (j : W) : y j - y jMin ≤ B := by
    have h := hy.2 j jMin
    unfold Q61CompactAssignmentSlack.normalize at h
    linarith only [h]
  have hstart : (fun i => x i + (-x iMax)) ≤ (fun _ => 0) := by
    intro i
    change x i + (-x iMax) ≤ 0
    simpa only [sub_eq_add_neg] using (sub_nonpos.mpr (hxMax i))
  have hcompare : endpointScores M (fun i => x i + (-x iMax)) p.edges ≤
      endpointScores M (fun _ => 0) p.edges :=
    endpointScores_mono M p.edges hstart
  rw [endpointScores_add_const] at hcompare
  have hphysical : y jMin - x iMax ≤ matrixMinimum M p.edges := by
    rw [matrixMinimum_eq_inf]
    apply Finset.le_inf' Finset.univ_nonempty _
    intro j _
    calc
      y jMin - x iMax ≤ y j - x iMax := sub_le_sub_right (hyMin j) _
      _ ≤ endpointScores M (fun _ => 0) p.edges j := by
        simpa only [y, sub_eq_add_neg] using hcompare j
  have hinput := sum_le_card_sub_one_mul (fun i => x iMax - x i) iMax
    (sub_self _) (hx.2 iMax)
  have houtput := sum_le_card_sub_one_mul (fun j => y j - y jMin) jMin
    (sub_self _) hySpread
  have herrors := add_le_add hinput houtput
  have hsum :
      (∑ i, (x iMax - x i)) + (∑ j, (y j - y jMin)) =
        ((∑ j, y j) - ∑ i, x i) - (y jMin - x iMax) * (Fintype.card W : ℝ) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hgain :
      (p.length : ℝ) * ((Fintype.card W : ℝ) * rate) + H s - H t -
          assignmentSlack M rate H s t p.edges x = (∑ j, y j) - ∑ i, x i := by
    simp only [assignmentSlack, EdgeGraph.Walk.edges_length, y]
    ring
  rw [hsum, ← hgain] at herrors
  have hcard : 0 < (Fintype.card W : ℝ) := by
    exact_mod_cast (Fintype.card_pos (α := W))
  calc
    _ = ((p.length : ℝ) * ((Fintype.card W : ℝ) * rate) + H s - H t -
          assignmentSlack M rate H s t p.edges x -
          2 * (((Fintype.card W : ℝ) - 1) * B)) / (Fintype.card W : ℝ) := by
      field_simp [hcard.ne'] <;> ring
    _ ≤ y jMin - x iMax := (div_le_iff₀ hcard).2 (by
      rw [two_mul]
      linarith only [herrors])
    _ ≤ matrixMinimum M p.edges := hphysical

/-- For a tight legal walk, the same word from physical zero scores and
with a free terminal Bob vertex earns at least the rate plus the potential
difference per Bob vertex, up to the two spread corrections. -/
theorem matrixMinimum_ge_of_tight_walk (σ : E → Equiv.Perm W)
    (hcap : ∀ e, assignmentCost (M e) (σ e) ≤
      (Fintype.card W : ℝ) * rate + H (G.source e) - H (G.target e))
    (o : W) {B : ℝ} (hrow : ∀ e i j k, M e i j - M e i k ≤ B)
    {s t : V} (p : G.Walk s t) (x : W → ℝ) (hx : x ∈ projectiveBox o B)
    (htight : TightAlong G M σ (fun _ => (Fintype.card W : ℝ) * rate) H x p) :
    (p.length : ℝ) * rate + (H s - H t) / (Fintype.card W : ℝ) -
        2 * (1 - 1 / (Fintype.card W : ℝ)) * B ≤ matrixMinimum M p.edges := by
  have hslack := (assignmentSlack_spec G M rate H σ hcap p x).2.mpr htight
  simpa only [hslack, sub_zero] using
    matrixMinimum_ge_of_assignmentSlack G M rate H o hrow p x hx

end

end Q61TightWalkPayoff
