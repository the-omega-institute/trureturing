/- GID: D5/S3/Observer/CubicGain/JMJPairLosing
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/JMJPairLosing
   mirror-E: none(waiver:native-jmj-pair-losing-characterization)
   anchors: []
   utility: none
   digest: Two complete worlds at either fourth JMJ child lose exactly through common drift and native continuation equalities. -/
import D5.S3.Observer.CubicGain.MixedTripleExclusion
/-! Losing pairs at the original clocks below the chronological JMJ history. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix Classical
namespace D5.S3.Observer.CubicGain.JMJPairLosing
open D5.S3.Observer.Linear.GainRay
open D5.S3.Observer.CubicGain.MixedTripleExclusion

private theorem losing_pair_of_suffix (n : ℕ) (W Z : World3) (hne : W ≠ Z)
    (v : List Bool)
    (he : ∀ u : List Bool, u ≠ [] → u.length ≤ n →
      readAt W (v ++ u) (v.length + u.length) =
        readAt Z (v ++ u) (v.length + u.length)) :
    Losing n {W, Z} v := by
  induction n generalizing v with
  | zero => simp [Losing, hne]
  | succ n ih =>
    refine ⟨by simp [hne], ?_⟩
    intro E
    have hE := he [E] (by simp) (by simp)
    have hs : responseSlice {W, Z} v E
        (readAt W (v ++ [E]) (v.length + 1)) = {W, Z} := by
      ext U
      simp only [responseSlice, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact And.left
      · intro hU
        refine ⟨hU, ?_⟩
        rcases hU with rfl | rfl
        · rfl
        · simpa using hE.symm
    refine ⟨readAt W (v ++ [E]) (v.length + 1), ?_⟩
    rw [hs]
    apply ih
    intro u hu hn
    have hh := he ([E] ++ u) (by simp) (by simp; omega)
    simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

private theorem jmj_trace_pos (W : World3) (i : Fin 4) :
    0 < Matrix.trace (acquisition ([true, false, true].take i.val) * W.source) := by
  have h00 := W.legal.1 0 0
  have h01 := W.legal.1 0 1
  have h10 := W.legal.1 1 0
  have h11 := W.legal.1 1 1
  fin_cases i <;>
    norm_num [acquisition, Raw,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
      Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two] <;> positivity

private theorem jmj_world_eq_of_source_drift (W Z : World3)
    (hp : W.source = Z.source) (hd : W.drift = Z.drift)
    (he : readings W [true, false, true] = readings Z [true, false, true]) : W = Z := by
  have hc : W.coeff = Z.coeff := by
    apply four_evaluations W.coeff Z.coeff (fun i : Fin 4 => (i.val : ℝ))
    · intro i j h
      apply Fin.ext
      change (i.val : ℝ) = (j.val : ℝ) at h
      exact_mod_cast h
    · intro i
      have hh := congrFun he i
      change (gain 3 W.coeff).eval (i.val : ℝ) *
          Matrix.trace (acquisition ([true, false, true].take i.val) * W.source) + W.drift =
        (gain 3 Z.coeff).eval (i.val : ℝ) *
          Matrix.trace (acquisition ([true, false, true].take i.val) * Z.source) + Z.drift at hh
      rw [← hp, ← hd] at hh
      exact mul_right_cancel₀ (ne_of_gt (jmj_trace_pos W i)) (add_right_cancel hh)
  cases W
  cases Z
  cases hp
  cases hc
  cases hd
  rfl

/-- Complete native pairs at either fourth child of the actual JMJ history.
The horizon is arbitrary; at horizon three the gain condition is exactly the
four zero samples of the two worlds at original clocks six and seven. -/
theorem jmj_pair_losing_iff (n : ℕ) (hn : 3 ≤ n) (E : Bool) (z v : ℝ)
    (W Z : World3) (hne : W ≠ Z)
    (hW : readings W [true, false, true, E] = ![0, 24, 48, z, v])
    (hZ : readings Z [true, false, true, E] = ![0, 24, 48, z, v]) :
    Losing n {W, Z} [true, false, true, E] ↔
      W.drift = Z.drift ∧
      (∀ j : ℕ, 2 ≤ j → j ≤ n →
        (gain 3 W.coeff).eval ((4 + j : ℕ) : ℝ) = 0 ∧
        (gain 3 Z.coeff).eval ((4 + j : ℕ) : ℝ) = 0) ∧
      (∀ F : Bool, readAt W [true, false, true, E, F] 5 =
        readAt Z [true, false, true, E, F] 5) := by
  have hcard : ({W, Z} : Finset World3).card = 2 := by simp [hne]
  have hmemW : W ∈ ({W, Z} : Finset World3) := by simp
  have hmemZ : Z ∈ ({W, Z} : Finset World3) := by simp
  constructor
  · intro hl
    have hd := pair_common_drift n {W, Z} [true, false, true, E] hcard hl hn W Z hmemW hmemZ
    have hp : W.source ≠ Z.source := by
      intro hp
      apply hne
      apply jmj_world_eq_of_source_drift W Z hp hd
      funext i
      have hi : i.val < 4 := i.isLt
      have hw := congrFun hW ⟨i.val, by change i.val < 5; omega⟩
      have hz := congrFun hZ ⟨i.val, by change i.val < 5; omega⟩
      have hh := hw.trans hz.symm
      fin_cases i <;> simpa [readings, readAt] using hh
    refine ⟨hd, ?_, ?_⟩
    · intro j hj hjn
      simpa using pair_gain_zero n {W, Z} [true, false, true, E] hcard hl hn
        W Z hmemW hmemZ hp j hj hjn
    · intro F
      simpa using (losing_pair_suffix n {W, Z} [true, false, true, E] hcard hl
        [F] (by simp; omega)).2 (by simp) W hmemW Z hmemZ
  · rintro ⟨hd, hz, hf⟩
    apply losing_pair_of_suffix n W Z hne
    intro u hu hun
    by_cases hu1 : u.length = 1
    · cases u with
      | nil => simp at hu1
      | cons F u =>
        have hut : u = [] := by simpa using hu1
        subst u
        simpa using hf F
    · have hu2 : 2 ≤ u.length := by
        have hu0 : u.length ≠ 0 := by simpa using hu
        omega
      obtain ⟨hw, hzz⟩ := hz u.length hu2 hun
      rw [read_concat, read_concat]
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
      rw [hw, hzz]
      simpa using hd

end D5.S3.Observer.CubicGain.JMJPairLosing
